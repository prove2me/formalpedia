-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1207_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:05:33.204978+00:00
-- url     : https://prove2.me/submissions/2d184bc1-0395-4db7-a39d-476ca1b34e2e

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
theorem support_rectangle_w1207_s0_0 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-935703853/5000000000 : ℝ)*x 0 + (6039428613/10000000000 : ℝ)*x 1 + (478863761/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (935703853/5000000000 : ℝ)^525 ≤ (10901902910491/100000000000000 : ℝ)^397 := by
    have hnat : (935703853 : ℕ)^525*100000000000000^397 ≤ 10901902910491^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935703853 5000000000 10901902910491 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6039428613/10000000000 : ℝ)^525 ≤ (12832904187389/25000000000000 : ℝ)^397 := by
    have hnat : (6039428613 : ℕ)^525*25000000000000^397 ≤ 12832904187389^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6039428613 10000000000 12832904187389 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478863761/1000000000 : ℝ)^525 ≤ (37766480323339/100000000000000 : ℝ)^397 := by
    have hnat : (478863761 : ℕ)^525*100000000000000^397 ≤ 37766480323339^397*1000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478863761 1000000000 37766480323339 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-935703853/5000000000 : ℝ), (6039428613/10000000000 : ℝ), (478863761/1000000000 : ℝ)] ![(10901902910491/100000000000000 : ℝ), (12832904187389/25000000000000 : ℝ), (37766480323339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-935703853/5000000000 : ℝ)|^525 ≤ (10901902910491/100000000000000 : ℝ)^397
        have hw : |(-935703853/5000000000 : ℝ)|=(935703853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6039428613/10000000000 : ℝ)|^525 ≤ (12832904187389/25000000000000 : ℝ)^397
        have hw : |(6039428613/10000000000 : ℝ)|=(6039428613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(478863761/1000000000 : ℝ)|^525 ≤ (37766480323339/100000000000000 : ℝ)^397
        have hw : |(478863761/1000000000 : ℝ)|=(478863761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s0_1 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5513131407/10000000000 : ℝ)*x 0 + (-2587411089/10000000000 : ℝ)*x 1 + (598579699/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513131407/10000000000 : ℝ)^525 ≤ (45500951678861/100000000000000 : ℝ)^397 := by
    have hnat : (5513131407 : ℕ)^525*100000000000000^397 ≤ 45500951678861^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513131407 10000000000 45500951678861 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587411089/10000000000 : ℝ)^525 ≤ (16732568171963/100000000000000 : ℝ)^397 := by
    have hnat : (2587411089 : ℕ)^525*100000000000000^397 ≤ 16732568171963^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587411089 10000000000 16732568171963 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598579699/1250000000 : ℝ)^525 ≤ (4720810016951/12500000000000 : ℝ)^397 := by
    have hnat : (598579699 : ℕ)^525*12500000000000^397 ≤ 4720810016951^397*1250000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598579699 1250000000 4720810016951 12500000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513131407/10000000000 : ℝ), (-2587411089/10000000000 : ℝ), (598579699/1250000000 : ℝ)] ![(45500951678861/100000000000000 : ℝ), (16732568171963/100000000000000 : ℝ), (4720810016951/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513131407/10000000000 : ℝ)|^525 ≤ (45500951678861/100000000000000 : ℝ)^397
        have hw : |(5513131407/10000000000 : ℝ)|=(5513131407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2587411089/10000000000 : ℝ)|^525 ≤ (16732568171963/100000000000000 : ℝ)^397
        have hw : |(-2587411089/10000000000 : ℝ)|=(2587411089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(598579699/1250000000 : ℝ)|^525 ≤ (4720810016951/12500000000000 : ℝ)^397
        have hw : |(598579699/1250000000 : ℝ)|=(598579699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s0_2 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2756565697/5000000000 : ℝ)*x 0 + (957727521/2000000000 : ℝ)*x 1 + (-2587411089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2756565697/5000000000 : ℝ)^525 ≤ (45500951536977/100000000000000 : ℝ)^397 := by
    have hnat : (2756565697 : ℕ)^525*100000000000000^397 ≤ 45500951536977^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756565697 5000000000 45500951536977 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (957727521/2000000000 : ℝ)^525 ≤ (4720810033899/12500000000000 : ℝ)^397 := by
    have hnat : (957727521 : ℕ)^525*12500000000000^397 ≤ 4720810033899^397*2000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957727521 2000000000 4720810033899 12500000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587411089/10000000000 : ℝ)^525 ≤ (16732568171963/100000000000000 : ℝ)^397 := by
    have hnat : (2587411089 : ℕ)^525*100000000000000^397 ≤ 16732568171963^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587411089 10000000000 16732568171963 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2756565697/5000000000 : ℝ), (957727521/2000000000 : ℝ), (-2587411089/10000000000 : ℝ)] ![(45500951536977/100000000000000 : ℝ), (4720810033899/12500000000000 : ℝ), (16732568171963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2756565697/5000000000 : ℝ)|^525 ≤ (45500951536977/100000000000000 : ℝ)^397
        have hw : |(2756565697/5000000000 : ℝ)|=(2756565697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(957727521/2000000000 : ℝ)|^525 ≤ (4720810033899/12500000000000 : ℝ)^397
        have hw : |(957727521/2000000000 : ℝ)|=(957727521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2587411089/10000000000 : ℝ)|^525 ≤ (16732568171963/100000000000000 : ℝ)^397
        have hw : |(-2587411089/10000000000 : ℝ)|=(2587411089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s0_3 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2097892169/5000000000 : ℝ)*x 0 + (3118256757/10000000000 : ℝ)*x 1 + (1409609539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097892169/5000000000 : ℝ)^525 ≤ (158551838811/500000000000 : ℝ)^397 := by
    have hnat : (2097892169 : ℕ)^525*500000000000^397 ≤ 158551838811^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097892169 5000000000 158551838811 500000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3118256757/10000000000 : ℝ)^525 ≤ (267700938817/1250000000000 : ℝ)^397 := by
    have hnat : (3118256757 : ℕ)^525*1250000000000^397 ≤ 267700938817^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118256757 10000000000 267700938817 1250000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1409609539/2500000000 : ℝ)^525 ≤ (23436778560933/50000000000000 : ℝ)^397 := by
    have hnat : (1409609539 : ℕ)^525*50000000000000^397 ≤ 23436778560933^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1409609539 2500000000 23436778560933 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097892169/5000000000 : ℝ), (3118256757/10000000000 : ℝ), (1409609539/2500000000 : ℝ)] ![(158551838811/500000000000 : ℝ), (267700938817/1250000000000 : ℝ), (23436778560933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097892169/5000000000 : ℝ)|^525 ≤ (158551838811/500000000000 : ℝ)^397
        have hw : |(2097892169/5000000000 : ℝ)|=(2097892169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3118256757/10000000000 : ℝ)|^525 ≤ (267700938817/1250000000000 : ℝ)^397
        have hw : |(3118256757/10000000000 : ℝ)|=(3118256757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1409609539/2500000000 : ℝ)|^525 ≤ (23436778560933/50000000000000 : ℝ)^397
        have hw : |(1409609539/2500000000 : ℝ)|=(1409609539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s0_4 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-938182617/5000000000 : ℝ)*x 0 + (964173999/2000000000 : ℝ)*x 1 + (750757297/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (938182617/5000000000 : ℝ)^525 ≤ (5470055406071/50000000000000 : ℝ)^397 := by
    have hnat : (938182617 : ℕ)^525*50000000000000^397 ≤ 5470055406071^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938182617 5000000000 5470055406071 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (964173999/2000000000 : ℝ)^525 ≤ (19051506043927/50000000000000 : ℝ)^397 := by
    have hnat : (964173999 : ℕ)^525*50000000000000^397 ≤ 19051506043927^397*2000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964173999 2000000000 19051506043927 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (750757297/1250000000 : ℝ)^525 ≤ (50956877073789/100000000000000 : ℝ)^397 := by
    have hnat : (750757297 : ℕ)^525*100000000000000^397 ≤ 50956877073789^397*1250000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750757297 1250000000 50956877073789 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-938182617/5000000000 : ℝ), (964173999/2000000000 : ℝ), (750757297/1250000000 : ℝ)] ![(5470055406071/50000000000000 : ℝ), (19051506043927/50000000000000 : ℝ), (50956877073789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-938182617/5000000000 : ℝ)|^525 ≤ (5470055406071/50000000000000 : ℝ)^397
        have hw : |(-938182617/5000000000 : ℝ)|=(938182617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(964173999/2000000000 : ℝ)|^525 ≤ (19051506043927/50000000000000 : ℝ)^397
        have hw : |(964173999/2000000000 : ℝ)|=(964173999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(750757297/1250000000 : ℝ)|^525 ≤ (50956877073789/100000000000000 : ℝ)^397
        have hw : |(750757297/1250000000 : ℝ)|=(750757297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s0_5 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5172961473/10000000000 : ℝ)*x 0 + (-171248603/1250000000 : ℝ)*x 1 + (6006059997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5172961473/10000000000 : ℝ)^525 ≤ (20912867643463/50000000000000 : ℝ)^397 := by
    have hnat : (5172961473 : ℕ)^525*50000000000000^397 ≤ 20912867643463^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172961473 10000000000 20912867643463 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171248603/1250000000 : ℝ)^525 ≤ (7217369441077/100000000000000 : ℝ)^397 := by
    have hnat : (171248603 : ℕ)^525*100000000000000^397 ≤ 7217369441077^397*1250000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171248603 1250000000 7217369441077 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6006059997/10000000000 : ℝ)^525 ≤ (50956895260957/100000000000000 : ℝ)^397 := by
    have hnat : (6006059997 : ℕ)^525*100000000000000^397 ≤ 50956895260957^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6006059997 10000000000 50956895260957 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5172961473/10000000000 : ℝ), (-171248603/1250000000 : ℝ), (6006059997/10000000000 : ℝ)] ![(20912867643463/50000000000000 : ℝ), (7217369441077/100000000000000 : ℝ), (50956895260957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5172961473/10000000000 : ℝ)|^525 ≤ (20912867643463/50000000000000 : ℝ)^397
        have hw : |(5172961473/10000000000 : ℝ)|=(5172961473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-171248603/1250000000 : ℝ)|^525 ≤ (7217369441077/100000000000000 : ℝ)^397
        have hw : |(-171248603/1250000000 : ℝ)|=(171248603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6006059997/10000000000 : ℝ)|^525 ≤ (50956895260957/100000000000000 : ℝ)^397
        have hw : |(6006059997/10000000000 : ℝ)|=(6006059997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s0_6 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1293240567/2500000000 : ℝ)*x 0 + (1501514719/2500000000 : ℝ)*x 1 + (-1369989409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293240567/2500000000 : ℝ)^525 ≤ (2614108986709/6250000000000 : ℝ)^397 := by
    have hnat : (1293240567 : ℕ)^525*6250000000000^397 ≤ 2614108986709^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293240567 2500000000 2614108986709 6250000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1501514719/2500000000 : ℝ)^525 ≤ (50956882683649/100000000000000 : ℝ)^397 := by
    have hnat : (1501514719 : ℕ)^525*100000000000000^397 ≤ 50956882683649^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501514719 2500000000 50956882683649 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369989409/10000000000 : ℝ)^525 ≤ (7217373516631/100000000000000 : ℝ)^397 := by
    have hnat : (1369989409 : ℕ)^525*100000000000000^397 ≤ 7217373516631^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369989409 10000000000 7217373516631 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293240567/2500000000 : ℝ), (1501514719/2500000000 : ℝ), (-1369989409/10000000000 : ℝ)] ![(2614108986709/6250000000000 : ℝ), (50956882683649/100000000000000 : ℝ), (7217373516631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293240567/2500000000 : ℝ)|^525 ≤ (2614108986709/6250000000000 : ℝ)^397
        have hw : |(1293240567/2500000000 : ℝ)|=(1293240567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1501514719/2500000000 : ℝ)|^525 ≤ (50956882683649/100000000000000 : ℝ)^397
        have hw : |(1501514719/2500000000 : ℝ)|=(1501514719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1369989409/10000000000 : ℝ)|^525 ≤ (7217373516631/100000000000000 : ℝ)^397
        have hw : |(-1369989409/10000000000 : ℝ)|=(1369989409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s0_7 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4205772071/10000000000 : ℝ)*x 0 + (5573497663/10000000000 : ℝ)*x 1 + (796372271/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205772071/10000000000 : ℝ)^525 ≤ (15905113745121/50000000000000 : ℝ)^397 := by
    have hnat : (4205772071 : ℕ)^525*50000000000000^397 ≤ 15905113745121^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205772071 10000000000 15905113745121 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5573497663/10000000000 : ℝ)^525 ≤ (9232191940659/20000000000000 : ℝ)^397 := by
    have hnat : (5573497663 : ℕ)^525*20000000000000^397 ≤ 9232191940659^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5573497663 10000000000 9232191940659 20000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796372271/2500000000 : ℝ)^525 ≤ (881152511841/4000000000000 : ℝ)^397 := by
    have hnat : (796372271 : ℕ)^525*4000000000000^397 ≤ 881152511841^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796372271 2500000000 881152511841 4000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205772071/10000000000 : ℝ), (5573497663/10000000000 : ℝ), (796372271/2500000000 : ℝ)] ![(15905113745121/50000000000000 : ℝ), (9232191940659/20000000000000 : ℝ), (881152511841/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205772071/10000000000 : ℝ)|^525 ≤ (15905113745121/50000000000000 : ℝ)^397
        have hw : |(4205772071/10000000000 : ℝ)|=(4205772071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5573497663/10000000000 : ℝ)|^525 ≤ (9232191940659/20000000000000 : ℝ)^397
        have hw : |(5573497663/10000000000 : ℝ)|=(5573497663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796372271/2500000000 : ℝ)|^525 ≤ (881152511841/4000000000000 : ℝ)^397
        have hw : |(796372271/2500000000 : ℝ)|=(796372271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1207_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (339/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1723/6250 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8399/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8399 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8399*1^2048 ≤ 0^2048*1^8399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8399 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8399/2048 : ℝ) ≤ (2333557409967186267/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8399 ≤ (2333557409967186267/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8399*100000000000000000000^2048 ≤ 2333557409967186267^2048*5^8399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2333557409967186267 100000000000000000000 8399 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2333557409967186267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8399 := by
      have hnat : (1 : ℕ)^2048*1^8399 ≤ 1^8399*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102333557409967186267/100000000000000000000 : ℝ) ≤ (2514101463040467/2500000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (102333557409967186267/100000000000000000000 : ℝ)^2048 ≤ (2514101463040467/2500000000000000 : ℝ)^8399 := by
      have hnat : (102333557409967186267 : ℕ)^2048*2500000000000000^8399 ≤ 2514101463040467^8399*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102333557409967186267 100000000000000000000 2514101463040467 2500000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514101463040467/2500000000000000 : ℝ)) (X := (102333557409967186267/100000000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52333557409967186267/50000000000000000000 : ℝ) ≤ (1264101463040467/1250000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (52333557409967186267/50000000000000000000 : ℝ)^2048 ≤ (1264101463040467/1250000000000000 : ℝ)^8399 := by
      have hnat : (52333557409967186267 : ℕ)^2048*1250000000000000^8399 ≤ 1264101463040467^8399*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52333557409967186267 50000000000000000000 1264101463040467 1250000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1264101463040467/1250000000000000 : ℝ)) (X := (52333557409967186267/50000000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14101463040467/1000000000000000 : ℝ)*(0 : ℝ))^(8399/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(14101463040467/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2333557409967186267/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14101463040467/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8399/2048 : ℝ) := by
    rw [show (1 : ℝ)+(14101463040467/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2514101463040467/2500000000000000 : ℝ) by norm_num, show 1+(2333557409967186267/100000000000000000000 : ℝ)+(0 : ℝ)=(102333557409967186267/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2333557409967186267/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14101463040467/1000000000000000 : ℝ)*(2/5 : ℝ))^(8399/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(14101463040467/1000000000000000 : ℝ)*(2/5 : ℝ)=(1264101463040467/1250000000000000 : ℝ) by norm_num, show 1+2*(2333557409967186267/100000000000000000000 : ℝ)=(52333557409967186267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14101463040467/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14101463040467/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14101463040467/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14101463040467/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14101463040467/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14101463040467/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-935703853/5000000000 : ℝ)*X 0 0+(6039428613/10000000000 : ℝ)*X 0 1+(478863761/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5513131407/10000000000 : ℝ)*X 1 0+(-2587411089/10000000000 : ℝ)*X 1 1+(598579699/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2756565697/5000000000 : ℝ)*X 2 0+(957727521/2000000000 : ℝ)*X 2 1+(-2587411089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2097892169/5000000000 : ℝ)*X 0 0+(3118256757/10000000000 : ℝ)*X 0 1+(1409609539/2500000000 : ℝ)*X 0 2+(2097892169/5000000000 : ℝ)*X 1 0+(3118256757/10000000000 : ℝ)*X 1 1+(1409609539/2500000000 : ℝ)*X 1 2+(2097892169/5000000000 : ℝ)*X 2 0+(3118256757/10000000000 : ℝ)*X 2 1+(1409609539/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-938182617/5000000000 : ℝ)*X 0 0+(964173999/2000000000 : ℝ)*X 0 1+(750757297/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5172961473/10000000000 : ℝ)*X 1 0+(-171248603/1250000000 : ℝ)*X 1 1+(6006059997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1293240567/2500000000 : ℝ)*X 2 0+(1501514719/2500000000 : ℝ)*X 2 1+(-1369989409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4205772071/10000000000 : ℝ)*X 0 0+(5573497663/10000000000 : ℝ)*X 0 1+(796372271/2500000000 : ℝ)*X 0 2+(4205772071/10000000000 : ℝ)*X 1 0+(5573497663/10000000000 : ℝ)*X 1 1+(796372271/2500000000 : ℝ)*X 1 2+(4205772071/10000000000 : ℝ)*X 2 0+(5573497663/10000000000 : ℝ)*X 2 1+(796372271/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64270022967456785851779/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56363117/100000000000000 : ℝ)*(base1) + (629397301/50000000000000 : ℝ)*(base19) + (292671599/25000000000000 : ℝ)*(base23) + (4311149/5000000000000 : ℝ)*(base24) + (28812809/10000000000000 : ℝ)*(upper3) + (598150809321179/100000000000000 : ℝ)*(major0) + (598150809321179/100000000000000 : ℝ)*(major1) + (598150809321179/100000000000000 : ℝ)*(major2) + (31979933396077/4000000000000 : ℝ)*(sp0) + (799499807983487/100000000000000 : ℝ)*(sp1) + (99937476233589/12500000000000 : ℝ)*(sp2) + (99199530412001/25000000000000 : ℝ)*(sp3) + (2788239281/100000000000000 : ℝ)*(sp4) + (1101233207/50000000000000 : ℝ)*(sp7) + (79360076095507/20000000000000 : ℝ)*(f.failure) + (99937633347261/12500000000000 : ℝ)*(f.sum) + (125819019949407/50000000000000000000000000000 : ℝ)*base66 + (846475035849407/100000000000000000000000000000 : ℝ)*base68 + (639127553449407/100000000000000000000000000000 : ℝ)*base70 + (647010418349407/100000000000000000000000000000 : ℝ)*base72 + (106457631199407/50000000000000000000000000000 : ℝ)*base74 + (1229605193249407/100000000000000000000000000000 : ℝ)*base76 + (209857250249407/100000000000000000000000000000 : ℝ)*base78 + (181381149849407/100000000000000000000000000000 : ℝ)*base80 + (131309775550593/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (12123049/2000000000000000000000 : ℝ)*base89 + (12123049/2000000000000000000000 : ℝ)*base91 + (12123049/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82668063029960548071099/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1795267709/100000000000000 : ℝ)*(base19) + (195352523/10000000000000 : ℝ)*(base23) + (1113319/25000000000000 : ℝ)*(base39) + (44010347/12500000000000 : ℝ)*(upper3) + (99883921/100000000000000 : ℝ)*(upper5) + (157813269671639/25000000000000 : ℝ)*(major0) + (157813269671639/25000000000000 : ℝ)*(major1) + (1972665856979/312500000000 : ℝ)*(major2) + (2060532303/50000000000000 : ℝ)*(sp1) + (2244967101/50000000000000 : ℝ)*(sp2) + (843746218538143/100000000000000 : ℝ)*(sp4) + (843740302205827/100000000000000 : ℝ)*(sp5) + (421869889765993/50000000000000 : ℝ)*(sp6) + (5234496424169/1250000000000 : ℝ)*(sp7) + (5234496424169/1250000000000 : ℝ)*(f.failure) + (421873111495709/50000000000000 : ℝ)*(f.sum) + (57987582300853/25000000000000000000000000000 : ℝ)*base65 + (1928345835261/625000000000000000000000000 : ℝ)*base67 + (303466626984587/25000000000000000000000000000 : ℝ)*base70 + (78707905261/625000000000000000000000000 : ℝ)*base71 + (144705809300853/25000000000000000000000000000 : ℝ)*base73 + (41382514559587/25000000000000000000000000000 : ℝ)*base76 + (38017384684587/25000000000000000000000000000 : ℝ)*base78 + (129805716565413/25000000000000000000000000000 : ℝ)*base79 + (27530758634587/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (379317/125000000000000000000 : ℝ)*base90 + (379317/125000000000000000000 : ℝ)*base92 + (379317/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1207_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (339/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1723/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1207_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1207_s1_0 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1035680403/5000000000 : ℝ)*x 0 + (568449087/1000000000 : ℝ)*x 1 + (5015581269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035680403/5000000000 : ℝ)^525 ≤ (12468212891253/100000000000000 : ℝ)^397 := by
    have hnat : (1035680403 : ℕ)^525*100000000000000^397 ≤ 12468212891253^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035680403 5000000000 12468212891253 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (568449087/1000000000 : ℝ)^525 ≤ (23690252625829/50000000000000 : ℝ)^397 := by
    have hnat : (568449087 : ℕ)^525*50000000000000^397 ≤ 23690252625829^397*1000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568449087 1000000000 23690252625829 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5015581269/10000000000 : ℝ)^525 ≤ (10037820461493/25000000000000 : ℝ)^397 := by
    have hnat : (5015581269 : ℕ)^525*25000000000000^397 ≤ 10037820461493^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015581269 10000000000 10037820461493 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1035680403/5000000000 : ℝ), (568449087/1000000000 : ℝ), (5015581269/10000000000 : ℝ)] ![(12468212891253/100000000000000 : ℝ), (23690252625829/50000000000000 : ℝ), (10037820461493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1035680403/5000000000 : ℝ)|^525 ≤ (12468212891253/100000000000000 : ℝ)^397
        have hw : |(-1035680403/5000000000 : ℝ)|=(1035680403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(568449087/1000000000 : ℝ)|^525 ≤ (23690252625829/50000000000000 : ℝ)^397
        have hw : |(568449087/1000000000 : ℝ)|=(568449087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5015581269/10000000000 : ℝ)|^525 ≤ (10037820461493/25000000000000 : ℝ)^397
        have hw : |(5015581269/10000000000 : ℝ)|=(5015581269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s1_1 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5415565367/10000000000 : ℝ)*x 0 + (-2431167069/10000000000 : ℝ)*x 1 + (1253895433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415565367/10000000000 : ℝ)^525 ≤ (44439148971259/100000000000000 : ℝ)^397 := by
    have hnat : (5415565367 : ℕ)^525*100000000000000^397 ≤ 44439148971259^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415565367 10000000000 44439148971259 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2431167069/10000000000 : ℝ)^525 ≤ (7704782134941/50000000000000 : ℝ)^397 := by
    have hnat : (2431167069 : ℕ)^525*50000000000000^397 ≤ 7704782134941^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431167069 10000000000 7704782134941 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1253895433/2500000000 : ℝ)^525 ≤ (2007564337373/5000000000000 : ℝ)^397 := by
    have hnat : (1253895433 : ℕ)^525*5000000000000^397 ≤ 2007564337373^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253895433 2500000000 2007564337373 5000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415565367/10000000000 : ℝ), (-2431167069/10000000000 : ℝ), (1253895433/2500000000 : ℝ)] ![(44439148971259/100000000000000 : ℝ), (7704782134941/50000000000000 : ℝ), (2007564337373/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415565367/10000000000 : ℝ)|^525 ≤ (44439148971259/100000000000000 : ℝ)^397
        have hw : |(5415565367/10000000000 : ℝ)|=(5415565367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2431167069/10000000000 : ℝ)|^525 ≤ (7704782134941/50000000000000 : ℝ)^397
        have hw : |(-2431167069/10000000000 : ℝ)|=(2431167069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1253895433/2500000000 : ℝ)|^525 ≤ (2007564337373/5000000000000 : ℝ)^397
        have hw : |(1253895433/2500000000 : ℝ)|=(1253895433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s1_2 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1353891031/2500000000 : ℝ)*x 0 + (2507791263/5000000000 : ℝ)*x 1 + (-97246707/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353891031/2500000000 : ℝ)^525 ≤ (8887827096563/20000000000000 : ℝ)^397 := by
    have hnat : (1353891031 : ℕ)^525*20000000000000^397 ≤ 8887827096563^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353891031 2500000000 8887827096563 20000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2507791263/5000000000 : ℝ)^525 ≤ (10037823788259/25000000000000 : ℝ)^397 := by
    have hnat : (2507791263 : ℕ)^525*25000000000000^397 ≤ 10037823788259^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507791263 5000000000 10037823788259 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97246707/400000000 : ℝ)^525 ≤ (3081913869867/20000000000000 : ℝ)^397 := by
    have hnat : (97246707 : ℕ)^525*20000000000000^397 ≤ 3081913869867^397*400000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97246707 400000000 3081913869867 20000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353891031/2500000000 : ℝ), (2507791263/5000000000 : ℝ), (-97246707/400000000 : ℝ)] ![(8887827096563/20000000000000 : ℝ), (10037823788259/25000000000000 : ℝ), (3081913869867/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353891031/2500000000 : ℝ)|^525 ≤ (8887827096563/20000000000000 : ℝ)^397
        have hw : |(1353891031/2500000000 : ℝ)|=(1353891031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2507791263/5000000000 : ℝ)|^525 ≤ (10037823788259/25000000000000 : ℝ)^397
        have hw : |(2507791263/5000000000 : ℝ)|=(2507791263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97246707/400000000 : ℝ)|^525 ≤ (3081913869867/20000000000000 : ℝ)^397
        have hw : |(-97246707/400000000 : ℝ)|=(97246707/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s1_3 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1077970361/2500000000 : ℝ)*x 0 + (3689080971/10000000000 : ℝ)*x 1 + (2518423899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077970361/2500000000 : ℝ)^525 ≤ (16437916497363/50000000000000 : ℝ)^397 := by
    have hnat : (1077970361 : ℕ)^525*50000000000000^397 ≤ 16437916497363^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077970361 2500000000 16437916497363 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3689080971/10000000000 : ℝ)^525 ≤ (6686899030171/25000000000000 : ℝ)^397 := by
    have hnat : (3689080971 : ℕ)^525*25000000000000^397 ≤ 6686899030171^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3689080971 10000000000 6686899030171 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2518423899/5000000000 : ℝ)^525 ≤ (5047071358229/12500000000000 : ℝ)^397 := by
    have hnat : (2518423899 : ℕ)^525*12500000000000^397 ≤ 5047071358229^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518423899 5000000000 5047071358229 12500000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077970361/2500000000 : ℝ), (3689080971/10000000000 : ℝ), (2518423899/5000000000 : ℝ)] ![(16437916497363/50000000000000 : ℝ), (6686899030171/25000000000000 : ℝ), (5047071358229/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077970361/2500000000 : ℝ)|^525 ≤ (16437916497363/50000000000000 : ℝ)^397
        have hw : |(1077970361/2500000000 : ℝ)|=(1077970361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3689080971/10000000000 : ℝ)|^525 ≤ (6686899030171/25000000000000 : ℝ)^397
        have hw : |(3689080971/10000000000 : ℝ)|=(3689080971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2518423899/5000000000 : ℝ)|^525 ≤ (5047071358229/12500000000000 : ℝ)^397
        have hw : |(2518423899/5000000000 : ℝ)|=(2518423899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s1_4 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-129504879/625000000 : ℝ)*x 0 + (502448829/1000000000 : ℝ)*x 1 + (5675413417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129504879/625000000 : ℝ)^525 ≤ (12473922638623/100000000000000 : ℝ)^397 := by
    have hnat : (129504879 : ℕ)^525*100000000000000^397 ≤ 12473922638623^397*625000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129504879 625000000 12473922638623 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502448829/1000000000 : ℝ)^525 ≤ (40245601821829/100000000000000 : ℝ)^397 := by
    have hnat : (502448829 : ℕ)^525*100000000000000^397 ≤ 40245601821829^397*1000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502448829 1000000000 40245601821829 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5675413417/10000000000 : ℝ)^525 ≤ (738757430143/1562500000000 : ℝ)^397 := by
    have hnat : (5675413417 : ℕ)^525*1562500000000^397 ≤ 738757430143^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675413417 10000000000 738757430143 1562500000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129504879/625000000 : ℝ), (502448829/1000000000 : ℝ), (5675413417/10000000000 : ℝ)] ![(12473922638623/100000000000000 : ℝ), (40245601821829/100000000000000 : ℝ), (738757430143/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129504879/625000000 : ℝ)|^525 ≤ (12473922638623/100000000000000 : ℝ)^397
        have hw : |(-129504879/625000000 : ℝ)|=(129504879/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502448829/1000000000 : ℝ)|^525 ≤ (40245601821829/100000000000000 : ℝ)^397
        have hw : |(502448829/1000000000 : ℝ)|=(502448829/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5675413417/10000000000 : ℝ)|^525 ≤ (738757430143/1562500000000 : ℝ)^397
        have hw : |(5675413417/10000000000 : ℝ)|=(5675413417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s1_5 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5243520927/10000000000 : ℝ)*x 0 + (-1771337941/10000000000 : ℝ)*x 1 + (709426357/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243520927/10000000000 : ℝ)^525 ≤ (21290917742183/50000000000000 : ℝ)^397 := by
    have hnat : (5243520927 : ℕ)^525*50000000000000^397 ≤ 21290917742183^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243520927 10000000000 21290917742183 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1771337941/10000000000 : ℝ)^525 ≤ (5068858595607/50000000000000 : ℝ)^397 := by
    have hnat : (1771337941 : ℕ)^525*50000000000000^397 ≤ 5068858595607^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1771337941 10000000000 5068858595607 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (709426357/1250000000 : ℝ)^525 ≤ (47280447315281/100000000000000 : ℝ)^397 := by
    have hnat : (709426357 : ℕ)^525*100000000000000^397 ≤ 47280447315281^397*1250000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709426357 1250000000 47280447315281 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243520927/10000000000 : ℝ), (-1771337941/10000000000 : ℝ), (709426357/1250000000 : ℝ)] ![(21290917742183/50000000000000 : ℝ), (5068858595607/50000000000000 : ℝ), (47280447315281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243520927/10000000000 : ℝ)|^525 ≤ (21290917742183/50000000000000 : ℝ)^397
        have hw : |(5243520927/10000000000 : ℝ)|=(5243520927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1771337941/10000000000 : ℝ)|^525 ≤ (5068858595607/50000000000000 : ℝ)^397
        have hw : |(-1771337941/10000000000 : ℝ)|=(1771337941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(709426357/1250000000 : ℝ)|^525 ≤ (47280447315281/100000000000000 : ℝ)^397
        have hw : |(709426357/1250000000 : ℝ)|=(709426357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s1_6 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5243521061/10000000000 : ℝ)*x 0 + (5675411321/10000000000 : ℝ)*x 1 + (-1771337073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243521061/10000000000 : ℝ)^525 ≤ (42581836923413/100000000000000 : ℝ)^397 := by
    have hnat : (5243521061 : ℕ)^525*100000000000000^397 ≤ 42581836923413^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243521061 10000000000 42581836923413 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5675411321/10000000000 : ℝ)^525 ≤ (9456090487613/20000000000000 : ℝ)^397 := by
    have hnat : (5675411321 : ℕ)^525*20000000000000^397 ≤ 9456090487613^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675411321 10000000000 9456090487613 20000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1771337073/10000000000 : ℝ)^525 ≤ (10137710621791/100000000000000 : ℝ)^397 := by
    have hnat : (1771337073 : ℕ)^525*100000000000000^397 ≤ 10137710621791^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1771337073 10000000000 10137710621791 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243521061/10000000000 : ℝ), (5675411321/10000000000 : ℝ), (-1771337073/10000000000 : ℝ)] ![(42581836923413/100000000000000 : ℝ), (9456090487613/20000000000000 : ℝ), (10137710621791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243521061/10000000000 : ℝ)|^525 ≤ (42581836923413/100000000000000 : ℝ)^397
        have hw : |(5243521061/10000000000 : ℝ)|=(5243521061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5675411321/10000000000 : ℝ)|^525 ≤ (9456090487613/20000000000000 : ℝ)^397
        have hw : |(5675411321/10000000000 : ℝ)|=(5675411321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1771337073/10000000000 : ℝ)|^525 ≤ (10137710621791/100000000000000 : ℝ)^397
        have hw : |(-1771337073/10000000000 : ℝ)|=(1771337073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s1_7 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (172533199/400000000 : ℝ)*x 0 + (5018899167/10000000000 : ℝ)*x 1 + (3707375901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172533199/400000000 : ℝ)^525 ≤ (16445219476613/50000000000000 : ℝ)^397 := by
    have hnat : (172533199 : ℕ)^525*50000000000000^397 ≤ 16445219476613^397*400000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172533199 400000000 16445219476613 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5018899167/10000000000 : ℝ)^525 ≤ (20093205038297/50000000000000 : ℝ)^397 := by
    have hnat : (5018899167 : ℕ)^525*50000000000000^397 ≤ 20093205038297^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018899167 10000000000 20093205038297 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3707375901/10000000000 : ℝ)^525 ≤ (13461575478223/50000000000000 : ℝ)^397 := by
    have hnat : (3707375901 : ℕ)^525*50000000000000^397 ≤ 13461575478223^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3707375901 10000000000 13461575478223 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172533199/400000000 : ℝ), (5018899167/10000000000 : ℝ), (3707375901/10000000000 : ℝ)] ![(16445219476613/50000000000000 : ℝ), (20093205038297/50000000000000 : ℝ), (13461575478223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172533199/400000000 : ℝ)|^525 ≤ (16445219476613/50000000000000 : ℝ)^397
        have hw : |(172533199/400000000 : ℝ)|=(172533199/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5018899167/10000000000 : ℝ)|^525 ≤ (20093205038297/50000000000000 : ℝ)^397
        have hw : |(5018899167/10000000000 : ℝ)|=(5018899167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3707375901/10000000000 : ℝ)|^525 ≤ (13461575478223/50000000000000 : ℝ)^397
        have hw : |(3707375901/10000000000 : ℝ)|=(3707375901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1207_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1723/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (339/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3003/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20149/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1723/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (339/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1723/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (339/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1723/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (339/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1723/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (339/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1723/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (339/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1723/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (339/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (339/50000 : ℝ) ^ (8399/2048 : ℝ) ≤ (7972454117/6250000000000000000 : ℝ) := by
    have hpowers : (339/50000 : ℝ)^8399 ≤ (7972454117/6250000000000000000 : ℝ)^2048 := by
      have hnat : (339 : ℕ)^8399*6250000000000000000^2048 ≤ 7972454117^2048*50000^8399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        339 50000 7972454117 6250000000000000000 8399 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (339/50000 : ℝ)) (X := (7972454117/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1723/6250 : ℝ) ^ (8399/2048 : ℝ) ≤ (253530634665802849/50000000000000000000 : ℝ) := by
    have hpowers : (1723/6250 : ℝ)^8399 ≤ (253530634665802849/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1723 : ℕ)^8399*50000000000000000000^2048 ≤ 253530634665802849^2048*6250^8399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1723 6250 253530634665802849 50000000000000000000 8399 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1723/6250 : ℝ)) (X := (253530634665802849/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125000007972454117/3125000000000000000 : ℝ) ≤ (5000000003110387/5000000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (3125000007972454117/3125000000000000000 : ℝ)^2048 ≤ (5000000003110387/5000000000000000 : ℝ)^8399 := by
      have hnat : (3125000007972454117 : ℕ)^2048*5000000000000000^8399 ≤ 5000000003110387^8399*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125000007972454117 3125000000000000000 5000000003110387 5000000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000003110387/5000000000000000 : ℝ)) (X := (3125000007972454117/3125000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10050706139689087157/10000000000000000000 : ℝ) ≤ (5006170239273437/5000000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (10050706139689087157/10000000000000000000 : ℝ)^2048 ≤ (5006170239273437/5000000000000000 : ℝ)^8399 := by
      have hnat : (10050706139689087157 : ℕ)^2048*5000000000000000^8399 ≤ 5006170239273437^8399*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10050706139689087157 10000000000000000000 5006170239273437 5000000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006170239273437/5000000000000000 : ℝ)) (X := (10050706139689087157/10000000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25253530634665802849/25000000000000000000 : ℝ) ≤ (5012340475436487/5000000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (25253530634665802849/25000000000000000000 : ℝ)^2048 ≤ (5012340475436487/5000000000000000 : ℝ)^8399 := by
      have hnat : (25253530634665802849 : ℕ)^2048*5000000000000000^8399 ≤ 5012340475436487^8399*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25253530634665802849 25000000000000000000 5012340475436487 5000000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012340475436487/5000000000000000 : ℝ)) (X := (25253530634665802849/25000000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7972454117/6250000000000000000 : ℝ) ≤ ((13444163324340121063/13445000000000000000 : ℝ)+2*(123404723261/26890000000000 : ℝ)*(339/50000 : ℝ))^(8399/2048 : ℝ) := by
    rw [show (13444163324340121063/13445000000000000000 : ℝ)+2*(123404723261/26890000000000 : ℝ)*(339/50000 : ℝ)=(5000000003110387/5000000000000000 : ℝ) by norm_num, show 1+2*(7972454117/6250000000000000000 : ℝ)=(3125000007972454117/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(253530634665802849/50000000000000000000 : ℝ)+(7972454117/6250000000000000000 : ℝ) ≤ ((13444163324340121063/13445000000000000000 : ℝ)+(123404723261/26890000000000 : ℝ)*((1723/6250 : ℝ)+(339/50000 : ℝ)))^(8399/2048 : ℝ) := by
    rw [show (13444163324340121063/13445000000000000000 : ℝ)+(123404723261/26890000000000 : ℝ)*((1723/6250 : ℝ)+(339/50000 : ℝ))=(5006170239273437/5000000000000000 : ℝ) by norm_num, show 1+(253530634665802849/50000000000000000000 : ℝ)+(7972454117/6250000000000000000 : ℝ)=(10050706139689087157/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(253530634665802849/50000000000000000000 : ℝ) ≤ ((13444163324340121063/13445000000000000000 : ℝ)+2*(123404723261/26890000000000 : ℝ)*(1723/6250 : ℝ))^(8399/2048 : ℝ) := by
    rw [show (13444163324340121063/13445000000000000000 : ℝ)+2*(123404723261/26890000000000 : ℝ)*(1723/6250 : ℝ)=(5012340475436487/5000000000000000 : ℝ) by norm_num, show 1+2*(253530634665802849/50000000000000000000 : ℝ)=(25253530634665802849/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13444163324340121063/13445000000000000000 : ℝ)*(X 1 0+X 2 0)+(123404723261/26890000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (339/50000 : ℝ)) (hi := (1723/6250 : ℝ)) (c := (13444163324340121063/13445000000000000000 : ℝ)) (alpha := (123404723261/26890000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13444163324340121063/13445000000000000000 : ℝ)*(X 0 1+X 2 1)+(123404723261/26890000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (339/50000 : ℝ)) (hi := (1723/6250 : ℝ)) (c := (13444163324340121063/13445000000000000000 : ℝ)) (alpha := (123404723261/26890000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13444163324340121063/13445000000000000000 : ℝ)*(X 0 2+X 1 2)+(123404723261/26890000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (339/50000 : ℝ)) (hi := (1723/6250 : ℝ)) (c := (13444163324340121063/13445000000000000000 : ℝ)) (alpha := (123404723261/26890000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1035680403/5000000000 : ℝ)*X 0 0+(568449087/1000000000 : ℝ)*X 0 1+(5015581269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5415565367/10000000000 : ℝ)*X 1 0+(-2431167069/10000000000 : ℝ)*X 1 1+(1253895433/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1353891031/2500000000 : ℝ)*X 2 0+(2507791263/5000000000 : ℝ)*X 2 1+(-97246707/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1077970361/2500000000 : ℝ)*X 0 0+(3689080971/10000000000 : ℝ)*X 0 1+(2518423899/5000000000 : ℝ)*X 0 2+(1077970361/2500000000 : ℝ)*X 1 0+(3689080971/10000000000 : ℝ)*X 1 1+(2518423899/5000000000 : ℝ)*X 1 2+(1077970361/2500000000 : ℝ)*X 2 0+(3689080971/10000000000 : ℝ)*X 2 1+(2518423899/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-129504879/625000000 : ℝ)*X 0 0+(502448829/1000000000 : ℝ)*X 0 1+(5675413417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5243520927/10000000000 : ℝ)*X 1 0+(-1771337941/10000000000 : ℝ)*X 1 1+(709426357/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5243521061/10000000000 : ℝ)*X 2 0+(5675411321/10000000000 : ℝ)*X 2 1+(-1771337073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((172533199/400000000 : ℝ)*X 0 0+(5018899167/10000000000 : ℝ)*X 0 1+(3707375901/10000000000 : ℝ)*X 0 2+(172533199/400000000 : ℝ)*X 1 0+(5018899167/10000000000 : ℝ)*X 1 1+(3707375901/10000000000 : ℝ)*X 1 2+(172533199/400000000 : ℝ)*X 2 0+(5018899167/10000000000 : ℝ)*X 2 1+(3707375901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3090824488940319057627/2689000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4073379/20000000000000 : ℝ)*(base16) + (208169769/50000000000000 : ℝ)*(base19) + (254926381/100000000000000 : ℝ)*(base23) + (43690727/50000000000000 : ℝ)*(upper2) + (124324211/100000000000000 : ℝ)*(upper3) + (1118474588112647/100000000000000 : ℝ)*(major0) + (1118474588112647/100000000000000 : ℝ)*(major1) + (1118474588112647/100000000000000 : ℝ)*(major2) + (747487499921871/50000000000000 : ℝ)*(sp0) + (298995343643407/20000000000000 : ℝ)*(sp1) + (747488449998543/50000000000000 : ℝ)*(sp2) + (741969980854867/100000000000000 : ℝ)*(sp3) + (86203189/4000000000000 : ℝ)*(sp4) + (2002132531/100000000000000 : ℝ)*(sp7) + (370985991493699/50000000000000 : ℝ)*(f.failure) + (373744288730867/25000000000000 : ℝ)*(f.sum) + (2608678038907/537800000000000000000000000 : ℝ)*base66 + (3414204305476883761/1344500000000000000000000000000000 : ℝ)*base67 + (7096367772304883761/1344500000000000000000000000000000 : ℝ)*base69 + (3093495946356116239/1344500000000000000000000000000000 : ℝ)*base72 + (14323528430743/2689000000000000000000000000 : ℝ)*base73 + (1085540857311616239/1344500000000000000000000000000000 : ℝ)*base76 + (5662453365001616239/1344500000000000000000000000000000 : ℝ)*base78 + (4909337452329883761/1344500000000000000000000000000000 : ℝ)*base79 + (4558274002551/2689000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (5662393/5000000000000000000000 : ℝ)*base89 + (5662393/5000000000000000000000 : ℝ)*base91 + (5662393/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2359986708800692615374962577/336125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (256033659/25000000000000 : ℝ)*(base19) + (1175971541/100000000000000 : ℝ)*(base23) + (430164203/100000000000000 : ℝ)*(base32) + (5070877/25000000000000 : ℝ)*(lower4) + (574686568875907/50000000000000 : ℝ)*(major0) + (574686568875907/50000000000000 : ℝ)*(major1) + (574686568875907/50000000000000 : ℝ)*(major2) + (178505547/25000000000000 : ℝ)*(sp0) + (1463548441/100000000000000 : ℝ)*(sp1) + (1857846973/50000000000000 : ℝ)*(sp2) + (1536275911263067/100000000000000 : ℝ)*(sp4) + (768137068801089/50000000000000 : ℝ)*(sp5) + (192033966702471/12500000000000 : ℝ)*(sp6) + (762468986015569/100000000000000 : ℝ)*(sp7) + (190617354044943/25000000000000 : ℝ)*(f.failure) + (307255325057051/20000000000000 : ℝ)*(f.sum) + (6872786593843/2689000000000000000000000000 : ℝ)*base66 + (933584176828179141/672250000000000000000000000000000 : ℝ)*base67 + (800593519312429141/672250000000000000000000000000000 : ℝ)*base69 + (2909711166105570859/672250000000000000000000000000000 : ℝ)*base72 + (1966236774691/672250000000000000000000000 : ℝ)*base73 + (964919876327179141/672250000000000000000000000000000 : ℝ)*base75 + (923417653358320859/672250000000000000000000000000000 : ℝ)*base78 + (2799903359746679141/672250000000000000000000000000000 : ℝ)*base79 + (3382540171013/2689000000000000000000000000 : ℝ)*base81 + (6564899/2500000000000000000000 : ℝ)*base90 + (6564899/2500000000000000000000 : ℝ)*base92 + (6564899/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1207_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1723/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (339/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3003/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20149/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1207_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1207_s2_0 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1060589417/5000000000 : ℝ)*x 0 + (5498871463/10000000000 : ℝ)*x 1 + (5169461967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060589417/5000000000 : ℝ)^525 ≤ (12866297476871/100000000000000 : ℝ)^397 := by
    have hnat : (1060589417 : ℕ)^525*100000000000000^397 ≤ 12866297476871^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060589417 5000000000 12866297476871 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5498871463/10000000000 : ℝ)^525 ≤ (22672690540703/50000000000000 : ℝ)^397 := by
    have hnat : (5498871463 : ℕ)^525*50000000000000^397 ≤ 22672690540703^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498871463 10000000000 22672690540703 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5169461967/10000000000 : ℝ)^525 ≤ (41788321427801/100000000000000 : ℝ)^397 := by
    have hnat : (5169461967 : ℕ)^525*100000000000000^397 ≤ 41788321427801^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169461967 10000000000 41788321427801 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1060589417/5000000000 : ℝ), (5498871463/10000000000 : ℝ), (5169461967/10000000000 : ℝ)] ![(12866297476871/100000000000000 : ℝ), (22672690540703/50000000000000 : ℝ), (41788321427801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1060589417/5000000000 : ℝ)|^525 ≤ (12866297476871/100000000000000 : ℝ)^397
        have hw : |(-1060589417/5000000000 : ℝ)|=(1060589417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5498871463/10000000000 : ℝ)|^525 ≤ (22672690540703/50000000000000 : ℝ)^397
        have hw : |(5498871463/10000000000 : ℝ)|=(5498871463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5169461967/10000000000 : ℝ)|^525 ≤ (41788321427801/100000000000000 : ℝ)^397
        have hw : |(5169461967/10000000000 : ℝ)|=(5169461967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s2_1 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1342780123/2500000000 : ℝ)*x 0 + (-143251161/625000000 : ℝ)*x 1 + (5169466673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342780123/2500000000 : ℝ)^525 ≤ (43957493625433/100000000000000 : ℝ)^397 := by
    have hnat : (1342780123 : ℕ)^525*100000000000000^397 ≤ 43957493625433^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342780123 2500000000 43957493625433 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (143251161/625000000 : ℝ)^525 ≤ (3563533655441/25000000000000 : ℝ)^397 := by
    have hnat : (143251161 : ℕ)^525*25000000000000^397 ≤ 3563533655441^397*625000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143251161 625000000 3563533655441 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5169466673/10000000000 : ℝ)^525 ≤ (20894185867513/50000000000000 : ℝ)^397 := by
    have hnat : (5169466673 : ℕ)^525*50000000000000^397 ≤ 20894185867513^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169466673 10000000000 20894185867513 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342780123/2500000000 : ℝ), (-143251161/625000000 : ℝ), (5169466673/10000000000 : ℝ)] ![(43957493625433/100000000000000 : ℝ), (3563533655441/25000000000000 : ℝ), (20894185867513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342780123/2500000000 : ℝ)|^525 ≤ (43957493625433/100000000000000 : ℝ)^397
        have hw : |(1342780123/2500000000 : ℝ)|=(1342780123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-143251161/625000000 : ℝ)|^525 ≤ (3563533655441/25000000000000 : ℝ)^397
        have hw : |(-143251161/625000000 : ℝ)|=(143251161/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5169466673/10000000000 : ℝ)|^525 ≤ (20894185867513/50000000000000 : ℝ)^397
        have hw : |(5169466673/10000000000 : ℝ)|=(5169466673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s2_2 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (42968981/80000000 : ℝ)*x 0 + (2584731861/5000000000 : ℝ)*x 1 + (-458403921/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42968981/80000000 : ℝ)^525 ≤ (21978758355159/50000000000000 : ℝ)^397 := by
    have hnat : (42968981 : ℕ)^525*50000000000000^397 ≤ 21978758355159^397*80000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42968981 80000000 21978758355159 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2584731861/5000000000 : ℝ)^525 ≤ (41788340188781/100000000000000 : ℝ)^397 := by
    have hnat : (2584731861 : ℕ)^525*100000000000000^397 ≤ 41788340188781^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584731861 5000000000 41788340188781 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458403921/2000000000 : ℝ)^525 ≤ (1781767885553/12500000000000 : ℝ)^397 := by
    have hnat : (458403921 : ℕ)^525*12500000000000^397 ≤ 1781767885553^397*2000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458403921 2000000000 1781767885553 12500000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42968981/80000000 : ℝ), (2584731861/5000000000 : ℝ), (-458403921/2000000000 : ℝ)] ![(21978758355159/50000000000000 : ℝ), (41788340188781/100000000000000 : ℝ), (1781767885553/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42968981/80000000 : ℝ)|^525 ≤ (21978758355159/50000000000000 : ℝ)^397
        have hw : |(42968981/80000000 : ℝ)|=(42968981/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2584731861/5000000000 : ℝ)|^525 ≤ (41788340188781/100000000000000 : ℝ)^397
        have hw : |(2584731861/5000000000 : ℝ)|=(2584731861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-458403921/2000000000 : ℝ)|^525 ≤ (1781767885553/12500000000000 : ℝ)^397
        have hw : |(-458403921/2000000000 : ℝ)|=(458403921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s2_3 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4346214279/10000000000 : ℝ)*x 0 + (4026726797/10000000000 : ℝ)*x 1 + (4690440887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346214279/10000000000 : ℝ)^525 ≤ (33222445738037/100000000000000 : ℝ)^397 := by
    have hnat : (4346214279 : ℕ)^525*100000000000000^397 ≤ 33222445738037^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346214279 10000000000 33222445738037 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4026726797/10000000000 : ℝ)^525 ≤ (3003181487747/10000000000000 : ℝ)^397 := by
    have hnat : (4026726797 : ℕ)^525*10000000000000^397 ≤ 3003181487747^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026726797 10000000000 3003181487747 10000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4690440887/10000000000 : ℝ)^525 ≤ (36745739368889/100000000000000 : ℝ)^397 := by
    have hnat : (4690440887 : ℕ)^525*100000000000000^397 ≤ 36745739368889^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4690440887 10000000000 36745739368889 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346214279/10000000000 : ℝ), (4026726797/10000000000 : ℝ), (4690440887/10000000000 : ℝ)] ![(33222445738037/100000000000000 : ℝ), (3003181487747/10000000000000 : ℝ), (36745739368889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346214279/10000000000 : ℝ)|^525 ≤ (33222445738037/100000000000000 : ℝ)^397
        have hw : |(4346214279/10000000000 : ℝ)|=(4346214279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4026726797/10000000000 : ℝ)|^525 ≤ (3003181487747/10000000000000 : ℝ)^397
        have hw : |(4026726797/10000000000 : ℝ)|=(4026726797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4690440887/10000000000 : ℝ)|^525 ≤ (36745739368889/100000000000000 : ℝ)^397
        have hw : |(4690440887/10000000000 : ℝ)|=(4690440887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s2_4 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121263619/10000000000 : ℝ)*x 0 + (3232271/6250000 : ℝ)*x 1 + (1099336001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121263619/10000000000 : ℝ)^525 ≤ (12866977567707/100000000000000 : ℝ)^397 := by
    have hnat : (2121263619 : ℕ)^525*100000000000000^397 ≤ 12866977567707^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121263619 10000000000 12866977567707 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3232271/6250000 : ℝ)^525 ≤ (41811537792579/100000000000000 : ℝ)^397 := by
    have hnat : (3232271 : ℕ)^525*100000000000000^397 ≤ 41811537792579^397*6250000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3232271 6250000 41811537792579 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099336001/2000000000 : ℝ)^525 ≤ (22660742311769/50000000000000 : ℝ)^397 := by
    have hnat : (1099336001 : ℕ)^525*50000000000000^397 ≤ 22660742311769^397*2000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099336001 2000000000 22660742311769 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121263619/10000000000 : ℝ), (3232271/6250000 : ℝ), (1099336001/2000000000 : ℝ)] ![(12866977567707/100000000000000 : ℝ), (41811537792579/100000000000000 : ℝ), (22660742311769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121263619/10000000000 : ℝ)|^525 ≤ (12866977567707/100000000000000 : ℝ)^397
        have hw : |(-2121263619/10000000000 : ℝ)|=(2121263619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3232271/6250000 : ℝ)|^525 ≤ (41811537792579/100000000000000 : ℝ)^397
        have hw : |(3232271/6250000 : ℝ)|=(3232271/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1099336001/2000000000 : ℝ)|^525 ≤ (22660742311769/50000000000000 : ℝ)^397
        have hw : |(1099336001/2000000000 : ℝ)|=(1099336001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s2_5 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5287185859/10000000000 : ℝ)*x 0 + (-1964803547/10000000000 : ℝ)*x 1 + (5496680031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287185859/10000000000 : ℝ)^525 ≤ (43051388349369/100000000000000 : ℝ)^397 := by
    have hnat : (5287185859 : ℕ)^525*100000000000000^397 ≤ 43051388349369^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287185859 10000000000 43051388349369 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1964803547/10000000000 : ℝ)^525 ≤ (2906781680137/25000000000000 : ℝ)^397 := by
    have hnat : (1964803547 : ℕ)^525*25000000000000^397 ≤ 2906781680137^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964803547 10000000000 2906781680137 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496680031/10000000000 : ℝ)^525 ≤ (45321484907033/100000000000000 : ℝ)^397 := by
    have hnat : (5496680031 : ℕ)^525*100000000000000^397 ≤ 45321484907033^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496680031 10000000000 45321484907033 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287185859/10000000000 : ℝ), (-1964803547/10000000000 : ℝ), (5496680031/10000000000 : ℝ)] ![(43051388349369/100000000000000 : ℝ), (2906781680137/25000000000000 : ℝ), (45321484907033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287185859/10000000000 : ℝ)|^525 ≤ (43051388349369/100000000000000 : ℝ)^397
        have hw : |(5287185859/10000000000 : ℝ)|=(5287185859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1964803547/10000000000 : ℝ)|^525 ≤ (2906781680137/25000000000000 : ℝ)^397
        have hw : |(-1964803547/10000000000 : ℝ)|=(1964803547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5496680031/10000000000 : ℝ)|^525 ≤ (45321484907033/100000000000000 : ℝ)^397
        have hw : |(5496680031/10000000000 : ℝ)|=(5496680031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s2_6 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5287186037/10000000000 : ℝ)*x 0 + (2748340029/5000000000 : ℝ)*x 1 + (-392960653/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287186037/10000000000 : ℝ)^525 ≤ (43051390266057/100000000000000 : ℝ)^397 := by
    have hnat : (5287186037 : ℕ)^525*100000000000000^397 ≤ 43051390266057^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287186037 10000000000 43051390266057 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2748340029/5000000000 : ℝ)^525 ≤ (5665185650179/12500000000000 : ℝ)^397 := by
    have hnat : (2748340029 : ℕ)^525*12500000000000^397 ≤ 5665185650179^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748340029 5000000000 5665185650179 12500000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (392960653/2000000000 : ℝ)^525 ≤ (5813562256853/50000000000000 : ℝ)^397 := by
    have hnat : (392960653 : ℕ)^525*50000000000000^397 ≤ 5813562256853^397*2000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392960653 2000000000 5813562256853 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287186037/10000000000 : ℝ), (2748340029/5000000000 : ℝ), (-392960653/2000000000 : ℝ)] ![(43051390266057/100000000000000 : ℝ), (5665185650179/12500000000000 : ℝ), (5813562256853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287186037/10000000000 : ℝ)|^525 ≤ (43051390266057/100000000000000 : ℝ)^397
        have hw : |(5287186037/10000000000 : ℝ)|=(5287186037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2748340029/5000000000 : ℝ)|^525 ≤ (5665185650179/12500000000000 : ℝ)^397
        have hw : |(2748340029/5000000000 : ℝ)|=(2748340029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-392960653/2000000000 : ℝ)|^525 ≤ (5813562256853/50000000000000 : ℝ)^397
        have hw : |(-392960653/2000000000 : ℝ)|=(392960653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s2_7 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4346387559/10000000000 : ℝ)*x 0 + (292879251/625000000 : ℝ)*x 1 + (125973159/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346387559/10000000000 : ℝ)^525 ≤ (664483947209/2000000000000 : ℝ)^397 := by
    have hnat : (4346387559 : ℕ)^525*2000000000000^397 ≤ 664483947209^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346387559 10000000000 664483947209 2000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (292879251/625000000 : ℝ)^525 ≤ (36700442988913/100000000000000 : ℝ)^397 := by
    have hnat : (292879251 : ℕ)^525*100000000000000^397 ≤ 36700442988913^397*625000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292879251 625000000 36700442988913 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125973159/312500000 : ℝ)^525 ≤ (30075359636783/100000000000000 : ℝ)^397 := by
    have hnat : (125973159 : ℕ)^525*100000000000000^397 ≤ 30075359636783^397*312500000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125973159 312500000 30075359636783 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346387559/10000000000 : ℝ), (292879251/625000000 : ℝ), (125973159/312500000 : ℝ)] ![(664483947209/2000000000000 : ℝ), (36700442988913/100000000000000 : ℝ), (30075359636783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346387559/10000000000 : ℝ)|^525 ≤ (664483947209/2000000000000 : ℝ)^397
        have hw : |(4346387559/10000000000 : ℝ)|=(4346387559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(292879251/625000000 : ℝ)|^525 ≤ (36700442988913/100000000000000 : ℝ)^397
        have hw : |(292879251/625000000 : ℝ)|=(292879251/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(125973159/312500000 : ℝ)|^525 ≤ (30075359636783/100000000000000 : ℝ)^397
        have hw : |(125973159/312500000 : ℝ)|=(125973159/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1207_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20149/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3003/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4677/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16317/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20149/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3003/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20149/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3003/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20149/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3003/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20149/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3003/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20149/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3003/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20149/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3003/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3003/50000 : ℝ) ^ (8399/2048 : ℝ) ≤ (979236916518639/100000000000000000000 : ℝ) := by
    have hpowers : (3003/50000 : ℝ)^8399 ≤ (979236916518639/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3003 : ℕ)^8399*100000000000000000000^2048 ≤ 979236916518639^2048*50000^8399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3003 50000 979236916518639 100000000000000000000 8399 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3003/50000 : ℝ)) (X := (979236916518639/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20149/100000 : ℝ) ^ (8399/2048 : ℝ) ≤ (140181903607683163/100000000000000000000 : ℝ) := by
    have hpowers : (20149/100000 : ℝ)^8399 ≤ (140181903607683163/100000000000000000000 : ℝ)^2048 := by
      have hnat : (20149 : ℕ)^8399*100000000000000000000^2048 ≤ 140181903607683163^2048*100000^8399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20149 100000 140181903607683163 100000000000000000000 8399 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20149/100000 : ℝ)) (X := (140181903607683163/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000979236916518639/50000000000000000000 : ℝ) ≤ (2000009550957759/2000000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (50000979236916518639/50000000000000000000 : ℝ)^2048 ≤ (2000009550957759/2000000000000000 : ℝ)^8399 := by
      have hnat : (50000979236916518639 : ℕ)^2048*2000000000000000^8399 ≤ 2000009550957759^8399*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000979236916518639 50000000000000000000 2000009550957759 2000000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000009550957759/2000000000000000 : ℝ)) (X := (50000979236916518639/50000000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50070580570262100901/50000000000000000000 : ℝ) ≤ (5001720108647883/5000000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (50070580570262100901/50000000000000000000 : ℝ)^2048 ≤ (5001720108647883/5000000000000000 : ℝ)^8399 := by
      have hnat : (50070580570262100901 : ℕ)^2048*5000000000000000^8399 ≤ 5001720108647883^8399*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50070580570262100901 50000000000000000000 5001720108647883 5000000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001720108647883/5000000000000000 : ℝ)) (X := (50070580570262100901/50000000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50140181903607683163/50000000000000000000 : ℝ) ≤ (10006832679802737/10000000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (50140181903607683163/50000000000000000000 : ℝ)^2048 ≤ (10006832679802737/10000000000000000 : ℝ)^8399 := by
      have hnat : (50140181903607683163 : ℕ)^2048*10000000000000000^8399 ≤ 10006832679802737^8399*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50140181903607683163 50000000000000000000 10006832679802737 10000000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006832679802737/10000000000000000 : ℝ)) (X := (50140181903607683163/50000000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(979236916518639/100000000000000000000 : ℝ) ≤ ((141389925136344192033/141430000000000000000 : ℝ)+2*(3392462506971/1414300000000000 : ℝ)*(3003/50000 : ℝ))^(8399/2048 : ℝ) := by
    rw [show (141389925136344192033/141430000000000000000 : ℝ)+2*(3392462506971/1414300000000000 : ℝ)*(3003/50000 : ℝ)=(2000009550957759/2000000000000000 : ℝ) by norm_num, show 1+2*(979236916518639/100000000000000000000 : ℝ)=(50000979236916518639/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(140181903607683163/100000000000000000000 : ℝ)+(979236916518639/100000000000000000000 : ℝ) ≤ ((141389925136344192033/141430000000000000000 : ℝ)+(3392462506971/1414300000000000 : ℝ)*((20149/100000 : ℝ)+(3003/50000 : ℝ)))^(8399/2048 : ℝ) := by
    rw [show (141389925136344192033/141430000000000000000 : ℝ)+(3392462506971/1414300000000000 : ℝ)*((20149/100000 : ℝ)+(3003/50000 : ℝ))=(5001720108647883/5000000000000000 : ℝ) by norm_num, show 1+(140181903607683163/100000000000000000000 : ℝ)+(979236916518639/100000000000000000000 : ℝ)=(50070580570262100901/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(140181903607683163/100000000000000000000 : ℝ) ≤ ((141389925136344192033/141430000000000000000 : ℝ)+2*(3392462506971/1414300000000000 : ℝ)*(20149/100000 : ℝ))^(8399/2048 : ℝ) := by
    rw [show (141389925136344192033/141430000000000000000 : ℝ)+2*(3392462506971/1414300000000000 : ℝ)*(20149/100000 : ℝ)=(10006832679802737/10000000000000000 : ℝ) by norm_num, show 1+2*(140181903607683163/100000000000000000000 : ℝ)=(50140181903607683163/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (141389925136344192033/141430000000000000000 : ℝ)*(X 1 0+X 2 0)+(3392462506971/1414300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (3003/50000 : ℝ)) (hi := (20149/100000 : ℝ)) (c := (141389925136344192033/141430000000000000000 : ℝ)) (alpha := (3392462506971/1414300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (141389925136344192033/141430000000000000000 : ℝ)*(X 0 1+X 2 1)+(3392462506971/1414300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (3003/50000 : ℝ)) (hi := (20149/100000 : ℝ)) (c := (141389925136344192033/141430000000000000000 : ℝ)) (alpha := (3392462506971/1414300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (141389925136344192033/141430000000000000000 : ℝ)*(X 0 2+X 1 2)+(3392462506971/1414300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (3003/50000 : ℝ)) (hi := (20149/100000 : ℝ)) (c := (141389925136344192033/141430000000000000000 : ℝ)) (alpha := (3392462506971/1414300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1060589417/5000000000 : ℝ)*X 0 0+(5498871463/10000000000 : ℝ)*X 0 1+(5169461967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1342780123/2500000000 : ℝ)*X 1 0+(-143251161/625000000 : ℝ)*X 1 1+(5169466673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42968981/80000000 : ℝ)*X 2 0+(2584731861/5000000000 : ℝ)*X 2 1+(-458403921/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4346214279/10000000000 : ℝ)*X 0 0+(4026726797/10000000000 : ℝ)*X 0 1+(4690440887/10000000000 : ℝ)*X 0 2+(4346214279/10000000000 : ℝ)*X 1 0+(4026726797/10000000000 : ℝ)*X 1 1+(4690440887/10000000000 : ℝ)*X 1 2+(4346214279/10000000000 : ℝ)*X 2 0+(4026726797/10000000000 : ℝ)*X 2 1+(4690440887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2121263619/10000000000 : ℝ)*X 0 0+(3232271/6250000 : ℝ)*X 0 1+(1099336001/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287185859/10000000000 : ℝ)*X 1 0+(-1964803547/10000000000 : ℝ)*X 1 1+(5496680031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287186037/10000000000 : ℝ)*X 2 0+(2748340029/5000000000 : ℝ)*X 2 1+(-392960653/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4346387559/10000000000 : ℝ)*X 0 0+(292879251/625000000 : ℝ)*X 0 1+(125973159/312500000 : ℝ)*X 0 2+(4346387559/10000000000 : ℝ)*X 1 0+(292879251/625000000 : ℝ)*X 1 1+(125973159/312500000 : ℝ)*X 1 2+(4346387559/10000000000 : ℝ)*X 2 0+(292879251/625000000 : ℝ)*X 2 1+(125973159/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52704751875125365560651563883/7071500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (312822269/20000000000000 : ℝ)*(base19) + (2344026543/100000000000000 : ℝ)*(base23) + (77951099/100000000000000 : ℝ)*(upper2) + (7597797/1000000000000 : ℝ)*(upper3) + (9580971/3125000000000 : ℝ)*(upper4) + (2271270670230061/100000000000000 : ℝ)*(major0) + (2271270670230061/100000000000000 : ℝ)*(major1) + (2271270670230061/100000000000000 : ℝ)*(major2) + (1517892726824399/50000000000000 : ℝ)*(sp0) + (3035827421080751/100000000000000 : ℝ)*(sp1) + (3035826641165553/100000000000000 : ℝ)*(sp2) + (753343799743487/50000000000000 : ℝ)*(sp3) + (21765771649/50000000000000 : ℝ)*(sp4) + (6126835911/25000000000000 : ℝ)*(sp7) + (753356053415309/50000000000000 : ℝ)*(f.failure) + (94869655787253/3125000000000 : ℝ)*(f.sum) + (165658314925411/70715000000000000000000000000 : ℝ)*base65 + (131175424644388404013/14143000000000000000000000000000000 : ℝ)*base67 + (97955272649258404013/14143000000000000000000000000000000 : ℝ)*base69 + (46105571301334404013/14143000000000000000000000000000000 : ℝ)*base71 + (87540001900941/70715000000000000000000000000 : ℝ)*base73 + (177273611346077404013/14143000000000000000000000000000000 : ℝ)*base75 + (136534680979315404013/14143000000000000000000000000000000 : ℝ)*base77 + (78966483685532404013/14143000000000000000000000000000000 : ℝ)*base79 + (1915332484171/1104921875000000000000000000 : ℝ)*base82 + (43851337/5000000000000000000000 : ℝ)*base90 + (43851337/5000000000000000000000 : ℝ)*base92 + (43851337/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92763908590428220311697101/11049218750000000000000000000000 : ℝ) := by norm_num
    linear_combination (2025710553/100000000000000 : ℝ)*(base19) + (2217200671/100000000000000 : ℝ)*(base23) + (9817029/100000000000000 : ℝ)*(upper2) + (1612053/625000000000 : ℝ)*(upper3) + (17163007/10000000000000 : ℝ)*(upper5) + (3596384256067/156250000000 : ℝ)*(major0) + (3596384256067/156250000000 : ℝ)*(major1) + (3596384256067/156250000000 : ℝ)*(major2) + (809640117/4000000000000 : ℝ)*(sp1) + (492176591/2000000000000 : ℝ)*(sp2) + (3076482636053659/100000000000000 : ℝ)*(sp4) + (1538230184670091/50000000000000 : ℝ)*(sp5) + (3076455810023439/100000000000000 : ℝ)*(sp6) + (1526888931861509/100000000000000 : ℝ)*(sp7) + (1526888931861509/100000000000000 : ℝ)*(f.failure) + (3076482636053659/100000000000000 : ℝ)*(f.sum) + (923995988967/7071500000000000000000000000 : ℝ)*base66 + (243442158186839211/22098437500000000000000000000000 : ℝ)*base67 + (315606772584150297/44196875000000000000000000000000 : ℝ)*base69 + (85167718905631547/44196875000000000000000000000000 : ℝ)*base71 + (47213110466663/7071500000000000000000000000 : ℝ)*base73 + (209713894341350297/44196875000000000000000000000000 : ℝ)*base75 + (140551435856932961/22098437500000000000000000000000 : ℝ)*base77 + (5616149316877167/2762304687500000000000000000000 : ℝ)*base79 + (8063897687439/2828600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (95027937/10000000000000000000000 : ℝ)*base90 + (95027937/10000000000000000000000 : ℝ)*base92 + (95027937/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1207_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20149/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3003/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1207_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1207_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1207_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1207_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1207_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1207_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
