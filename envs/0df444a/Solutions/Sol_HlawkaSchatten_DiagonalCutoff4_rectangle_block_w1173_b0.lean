-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1173_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:46:41.10871+00:00
-- url     : https://prove2.me/submissions/34e1d7e1-af6d-4e63-89c5-fc70bd85ce55

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
theorem support_rectangle_w1173_s0_0 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-235254819/1250000000 : ℝ)*x 0 + (604719279/1000000000 : ℝ)*x 1 + (1196095039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235254819/1250000000 : ℝ)^4183 ≤ (342252823487/3125000000000 : ℝ)^3159 := by
    have hnat : (235254819 : ℕ)^4183*3125000000000^3159 ≤ 342252823487^3159*1250000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235254819 1250000000 342252823487 3125000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604719279/1000000000 : ℝ)^4183 ≤ (51374047346903/100000000000000 : ℝ)^3159 := by
    have hnat : (604719279 : ℕ)^4183*100000000000000^3159 ≤ 51374047346903^3159*1000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604719279 1000000000 51374047346903 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196095039/2500000000 : ℝ)^4183 ≤ (18836931145719/50000000000000 : ℝ)^3159 := by
    have hnat : (1196095039 : ℕ)^4183*50000000000000^3159 ≤ 18836931145719^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196095039 2500000000 18836931145719 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235254819/1250000000 : ℝ), (604719279/1000000000 : ℝ), (1196095039/2500000000 : ℝ)] ![(342252823487/3125000000000 : ℝ), (51374047346903/100000000000000 : ℝ), (18836931145719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235254819/1250000000 : ℝ)|^4183 ≤ (342252823487/3125000000000 : ℝ)^3159
        have hw : |(-235254819/1250000000 : ℝ)|=(235254819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(604719279/1000000000 : ℝ)|^4183 ≤ (51374047346903/100000000000000 : ℝ)^3159
        have hw : |(604719279/1000000000 : ℝ)|=(604719279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1196095039/2500000000 : ℝ)|^4183 ≤ (18836931145719/50000000000000 : ℝ)^3159
        have hw : |(1196095039/2500000000 : ℝ)|=(1196095039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s0_1 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1378761779/2500000000 : ℝ)*x 0 + (-651467851/2500000000 : ℝ)*x 1 + (2392190101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378761779/2500000000 : ℝ)^4183 ≤ (1818995270641/4000000000000 : ℝ)^3159 := by
    have hnat : (1378761779 : ℕ)^4183*4000000000000^3159 ≤ 1818995270641^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378761779 2500000000 1818995270641 4000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651467851/2500000000 : ℝ)^4183 ≤ (8425627722417/50000000000000 : ℝ)^3159 := by
    have hnat : (651467851 : ℕ)^4183*50000000000000^3159 ≤ 8425627722417^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651467851 2500000000 8425627722417 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2392190101/5000000000 : ℝ)^4183 ≤ (37673862771073/100000000000000 : ℝ)^3159 := by
    have hnat : (2392190101 : ℕ)^4183*100000000000000^3159 ≤ 37673862771073^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2392190101 5000000000 37673862771073 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378761779/2500000000 : ℝ), (-651467851/2500000000 : ℝ), (2392190101/5000000000 : ℝ)] ![(1818995270641/4000000000000 : ℝ), (8425627722417/50000000000000 : ℝ), (37673862771073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378761779/2500000000 : ℝ)|^4183 ≤ (1818995270641/4000000000000 : ℝ)^3159
        have hw : |(1378761779/2500000000 : ℝ)|=(1378761779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-651467851/2500000000 : ℝ)|^4183 ≤ (8425627722417/50000000000000 : ℝ)^3159
        have hw : |(-651467851/2500000000 : ℝ)|=(651467851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2392190101/5000000000 : ℝ)|^4183 ≤ (37673862771073/100000000000000 : ℝ)^3159
        have hw : |(2392190101/5000000000 : ℝ)|=(2392190101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s0_2 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5515046641/10000000000 : ℝ)*x 0 + (4784380619/10000000000 : ℝ)*x 1 + (-1302935751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5515046641/10000000000 : ℝ)^4183 ≤ (22737438289883/50000000000000 : ℝ)^3159 := by
    have hnat : (5515046641 : ℕ)^4183*50000000000000^3159 ≤ 22737438289883^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515046641 10000000000 22737438289883 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4784380619/10000000000 : ℝ)^4183 ≤ (7534773423813/20000000000000 : ℝ)^3159 := by
    have hnat : (4784380619 : ℕ)^4183*20000000000000^3159 ≤ 7534773423813^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4784380619 10000000000 7534773423813 20000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1302935751/5000000000 : ℝ)^4183 ≤ (2106407035499/12500000000000 : ℝ)^3159 := by
    have hnat : (1302935751 : ℕ)^4183*12500000000000^3159 ≤ 2106407035499^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302935751 5000000000 2106407035499 12500000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5515046641/10000000000 : ℝ), (4784380619/10000000000 : ℝ), (-1302935751/5000000000 : ℝ)] ![(22737438289883/50000000000000 : ℝ), (7534773423813/20000000000000 : ℝ), (2106407035499/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5515046641/10000000000 : ℝ)|^4183 ≤ (22737438289883/50000000000000 : ℝ)^3159
        have hw : |(5515046641/10000000000 : ℝ)|=(5515046641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4784380619/10000000000 : ℝ)|^4183 ≤ (7534773423813/20000000000000 : ℝ)^3159
        have hw : |(4784380619/10000000000 : ℝ)|=(4784380619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1302935751/5000000000 : ℝ)|^4183 ≤ (2106407035499/12500000000000 : ℝ)^3159
        have hw : |(-1302935751/5000000000 : ℝ)|=(1302935751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s0_3 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (839699117/2000000000 : ℝ)*x 0 + (3119685963/10000000000 : ℝ)*x 1 + (28236517/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839699117/2000000000 : ℝ)^4183 ≤ (31689713507137/100000000000000 : ℝ)^3159 := by
    have hnat : (839699117 : ℕ)^4183*100000000000000^3159 ≤ 31689713507137^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839699117 2000000000 31689713507137 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3119685963/10000000000 : ℝ)^4183 ≤ (21385789844689/100000000000000 : ℝ)^3159 := by
    have hnat : (3119685963 : ℕ)^4183*100000000000000^3159 ≤ 21385789844689^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3119685963 10000000000 21385789844689 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28236517/50000000 : ℝ)^4183 ≤ (23462248321913/50000000000000 : ℝ)^3159 := by
    have hnat : (28236517 : ℕ)^4183*50000000000000^3159 ≤ 23462248321913^3159*50000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28236517 50000000 23462248321913 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839699117/2000000000 : ℝ), (3119685963/10000000000 : ℝ), (28236517/50000000 : ℝ)] ![(31689713507137/100000000000000 : ℝ), (21385789844689/100000000000000 : ℝ), (23462248321913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839699117/2000000000 : ℝ)|^4183 ≤ (31689713507137/100000000000000 : ℝ)^3159
        have hw : |(839699117/2000000000 : ℝ)|=(839699117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3119685963/10000000000 : ℝ)|^4183 ≤ (21385789844689/100000000000000 : ℝ)^3159
        have hw : |(3119685963/10000000000 : ℝ)|=(3119685963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28236517/50000000 : ℝ)|^4183 ≤ (23462248321913/50000000000000 : ℝ)^3159
        have hw : |(28236517/50000000 : ℝ)|=(28236517/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s0_4 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-943546489/5000000000 : ℝ)*x 0 + (1204235307/2500000000 : ℝ)*x 1 + (1503371273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943546489/5000000000 : ℝ)^4183 ≤ (109910547043/1000000000000 : ℝ)^3159 := by
    have hnat : (943546489 : ℕ)^4183*1000000000000^3159 ≤ 109910547043^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943546489 5000000000 109910547043 1000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1204235307/2500000000 : ℝ)^4183 ≤ (19006872648393/50000000000000 : ℝ)^3159 := by
    have hnat : (1204235307 : ℕ)^4183*50000000000000^3159 ≤ 19006872648393^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204235307 2500000000 19006872648393 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1503371273/2500000000 : ℝ)^4183 ≤ (6374399997543/12500000000000 : ℝ)^3159 := by
    have hnat : (1503371273 : ℕ)^4183*12500000000000^3159 ≤ 6374399997543^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503371273 2500000000 6374399997543 12500000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-943546489/5000000000 : ℝ), (1204235307/2500000000 : ℝ), (1503371273/2500000000 : ℝ)] ![(109910547043/1000000000000 : ℝ), (19006872648393/50000000000000 : ℝ), (6374399997543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-943546489/5000000000 : ℝ)|^4183 ≤ (109910547043/1000000000000 : ℝ)^3159
        have hw : |(-943546489/5000000000 : ℝ)|=(943546489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1204235307/2500000000 : ℝ)|^4183 ≤ (19006872648393/50000000000000 : ℝ)^3159
        have hw : |(1204235307/2500000000 : ℝ)|=(1204235307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1503371273/2500000000 : ℝ)|^4183 ≤ (6374399997543/12500000000000 : ℝ)^3159
        have hw : |(1503371273/2500000000 : ℝ)|=(1503371273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s0_5 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129294109/250000000 : ℝ)*x 0 + (-1376766619/10000000000 : ℝ)*x 1 + (6013484847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129294109/250000000 : ℝ)^4183 ≤ (41765126668329/100000000000000 : ℝ)^3159 := by
    have hnat : (129294109 : ℕ)^4183*100000000000000^3159 ≤ 41765126668329^3159*250000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129294109 250000000 41765126668329 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376766619/10000000000 : ℝ)^4183 ≤ (7239676089831/100000000000000 : ℝ)^3159 := by
    have hnat : (1376766619 : ℕ)^4183*100000000000000^3159 ≤ 7239676089831^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376766619 10000000000 7239676089831 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6013484847/10000000000 : ℝ)^4183 ≤ (50995197229237/100000000000000 : ℝ)^3159 := by
    have hnat : (6013484847 : ℕ)^4183*100000000000000^3159 ≤ 50995197229237^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6013484847 10000000000 50995197229237 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129294109/250000000 : ℝ), (-1376766619/10000000000 : ℝ), (6013484847/10000000000 : ℝ)] ![(41765126668329/100000000000000 : ℝ), (7239676089831/100000000000000 : ℝ), (50995197229237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129294109/250000000 : ℝ)|^4183 ≤ (41765126668329/100000000000000 : ℝ)^3159
        have hw : |(129294109/250000000 : ℝ)|=(129294109/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1376766619/10000000000 : ℝ)|^4183 ≤ (7239676089831/100000000000000 : ℝ)^3159
        have hw : |(-1376766619/10000000000 : ℝ)|=(1376766619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6013484847/10000000000 : ℝ)|^4183 ≤ (50995197229237/100000000000000 : ℝ)^3159
        have hw : |(6013484847/10000000000 : ℝ)|=(6013484847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s0_6 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2585882159/5000000000 : ℝ)*x 0 + (6013484961/10000000000 : ℝ)*x 1 + (-1376766499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585882159/5000000000 : ℝ)^4183 ≤ (41765126219209/100000000000000 : ℝ)^3159 := by
    have hnat : (2585882159 : ℕ)^4183*100000000000000^3159 ≤ 41765126219209^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585882159 5000000000 41765126219209 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6013484961/10000000000 : ℝ)^4183 ≤ (1593599953417/3125000000000 : ℝ)^3159 := by
    have hnat : (6013484961 : ℕ)^4183*3125000000000^3159 ≤ 1593599953417^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6013484961 10000000000 1593599953417 3125000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1376766499/10000000000 : ℝ)^4183 ≤ (723967525427/10000000000000 : ℝ)^3159 := by
    have hnat : (1376766499 : ℕ)^4183*10000000000000^3159 ≤ 723967525427^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376766499 10000000000 723967525427 10000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585882159/5000000000 : ℝ), (6013484961/10000000000 : ℝ), (-1376766499/10000000000 : ℝ)] ![(41765126219209/100000000000000 : ℝ), (1593599953417/3125000000000 : ℝ), (723967525427/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585882159/5000000000 : ℝ)|^4183 ≤ (41765126219209/100000000000000 : ℝ)^3159
        have hw : |(2585882159/5000000000 : ℝ)|=(2585882159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6013484961/10000000000 : ℝ)|^4183 ≤ (1593599953417/3125000000000 : ℝ)^3159
        have hw : |(6013484961/10000000000 : ℝ)|=(6013484961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1376766499/10000000000 : ℝ)|^4183 ≤ (723967525427/10000000000000 : ℝ)^3159
        have hw : |(-1376766499/10000000000 : ℝ)|=(1376766499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s0_7 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4208613323/10000000000 : ℝ)*x 0 + (1395532639/2500000000 : ℝ)*x 1 + (3187154929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208613323/10000000000 : ℝ)^4183 ≤ (31790875128551/100000000000000 : ℝ)^3159 := by
    have hnat : (4208613323 : ℕ)^4183*100000000000000^3159 ≤ 31790875128551^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208613323 10000000000 31790875128551 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1395532639/2500000000 : ℝ)^4183 ≤ (23104384162441/50000000000000 : ℝ)^3159 := by
    have hnat : (1395532639 : ℕ)^4183*50000000000000^3159 ≤ 23104384162441^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395532639 2500000000 23104384162441 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3187154929/10000000000 : ℝ)^4183 ≤ (11000178264879/50000000000000 : ℝ)^3159 := by
    have hnat : (3187154929 : ℕ)^4183*50000000000000^3159 ≤ 11000178264879^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3187154929 10000000000 11000178264879 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208613323/10000000000 : ℝ), (1395532639/2500000000 : ℝ), (3187154929/10000000000 : ℝ)] ![(31790875128551/100000000000000 : ℝ), (23104384162441/50000000000000 : ℝ), (11000178264879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208613323/10000000000 : ℝ)|^4183 ≤ (31790875128551/100000000000000 : ℝ)^3159
        have hw : |(4208613323/10000000000 : ℝ)|=(4208613323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1395532639/2500000000 : ℝ)|^4183 ≤ (23104384162441/50000000000000 : ℝ)^3159
        have hw : |(1395532639/2500000000 : ℝ)|=(1395532639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3187154929/10000000000 : ℝ)|^4183 ≤ (11000178264879/50000000000000 : ℝ)^3159
        have hw : |(3187154929/10000000000 : ℝ)|=(3187154929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1173_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (27/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27697/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8365/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8365 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8365*1^2048 ≤ 0^2048*1^8365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8365 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8365/2048 : ℝ) ≤ (1184663260575430747/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8365 ≤ (1184663260575430747/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8365*50000000000000000000^2048 ≤ 1184663260575430747^2048*5^8365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1184663260575430747 50000000000000000000 8365 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1184663260575430747/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8365 := by
      have hnat : (1 : ℕ)^2048*1^8365 ≤ 1^8365*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51184663260575430747/50000000000000000000 : ℝ) ≤ (10057496262108669/10000000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (51184663260575430747/50000000000000000000 : ℝ)^2048 ≤ (10057496262108669/10000000000000000 : ℝ)^8365 := by
      have hnat : (51184663260575430747 : ℕ)^2048*10000000000000000^8365 ≤ 10057496262108669^8365*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51184663260575430747 50000000000000000000 10057496262108669 10000000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10057496262108669/10000000000000000 : ℝ)) (X := (51184663260575430747/50000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26184663260575430747/25000000000000000000 : ℝ) ≤ (5057496262108669/5000000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (26184663260575430747/25000000000000000000 : ℝ)^2048 ≤ (5057496262108669/5000000000000000 : ℝ)^8365 := by
      have hnat : (26184663260575430747 : ℕ)^2048*5000000000000000^8365 ≤ 5057496262108669^8365*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26184663260575430747 25000000000000000000 5057496262108669 5000000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5057496262108669/5000000000000000 : ℝ)) (X := (26184663260575430747/25000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(57496262108669/4000000000000000 : ℝ)*(0 : ℝ))^(8365/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(57496262108669/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1184663260575430747/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(57496262108669/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8365/2048 : ℝ) := by
    rw [show (1 : ℝ)+(57496262108669/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10057496262108669/10000000000000000 : ℝ) by norm_num, show 1+(1184663260575430747/50000000000000000000 : ℝ)+(0 : ℝ)=(51184663260575430747/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1184663260575430747/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(57496262108669/4000000000000000 : ℝ)*(2/5 : ℝ))^(8365/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(57496262108669/4000000000000000 : ℝ)*(2/5 : ℝ)=(5057496262108669/5000000000000000 : ℝ) by norm_num, show 1+2*(1184663260575430747/50000000000000000000 : ℝ)=(26184663260575430747/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(57496262108669/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57496262108669/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(57496262108669/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57496262108669/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(57496262108669/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57496262108669/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-235254819/1250000000 : ℝ)*X 0 0+(604719279/1000000000 : ℝ)*X 0 1+(1196095039/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1378761779/2500000000 : ℝ)*X 1 0+(-651467851/2500000000 : ℝ)*X 1 1+(2392190101/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5515046641/10000000000 : ℝ)*X 2 0+(4784380619/10000000000 : ℝ)*X 2 1+(-1302935751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((839699117/2000000000 : ℝ)*X 0 0+(3119685963/10000000000 : ℝ)*X 0 1+(28236517/50000000 : ℝ)*X 0 2+(839699117/2000000000 : ℝ)*X 1 0+(3119685963/10000000000 : ℝ)*X 1 1+(28236517/50000000 : ℝ)*X 1 2+(839699117/2000000000 : ℝ)*X 2 0+(3119685963/10000000000 : ℝ)*X 2 1+(28236517/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-943546489/5000000000 : ℝ)*X 0 0+(1204235307/2500000000 : ℝ)*X 0 1+(1503371273/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((129294109/250000000 : ℝ)*X 1 0+(-1376766619/10000000000 : ℝ)*X 1 1+(6013484847/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2585882159/5000000000 : ℝ)*X 2 0+(6013484961/10000000000 : ℝ)*X 2 1+(-1376766499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4208613323/10000000000 : ℝ)*X 0 0+(1395532639/2500000000 : ℝ)*X 0 1+(3187154929/10000000000 : ℝ)*X 0 2+(4208613323/10000000000 : ℝ)*X 1 0+(1395532639/2500000000 : ℝ)*X 1 1+(3187154929/10000000000 : ℝ)*X 1 2+(4208613323/10000000000 : ℝ)*X 2 0+(1395532639/2500000000 : ℝ)*X 2 1+(3187154929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (688048877175619624705641/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22957303/100000000000000 : ℝ)*(base1) + (1864336903/100000000000000 : ℝ)*(base19) + (333325109/20000000000000 : ℝ)*(base23) + (129507303/100000000000000 : ℝ)*(base24) + (239249167/50000000000000 : ℝ)*(upper3) + (593764221490337/100000000000000 : ℝ)*(major0) + (593764221490337/100000000000000 : ℝ)*(major1) + (593764221490337/100000000000000 : ℝ)*(major2) + (79188960726933/10000000000000 : ℝ)*(sp0) + (6335133426941/800000000000 : ℝ)*(sp1) + (4949323416073/625000000000 : ℝ)*(sp2) + (395631342909857/100000000000000 : ℝ)*(sp3) + (1583357/40000000000 : ℝ)*(sp4) + (3305059357/100000000000000 : ℝ)*(sp7) + (395634670926517/100000000000000 : ℝ)*(f.failure) + (49493346419033/6250000000000 : ℝ)*(f.sum) + (327121528231453/200000000000000000000000000000 : ℝ)*base65 + (458497234231453/400000000000000000000000000000 : ℝ)*base67 + (425301454231453/400000000000000000000000000000 : ℝ)*base69 + (1264200234968547/400000000000000000000000000000 : ℝ)*base72 + (776054570831453/200000000000000000000000000000 : ℝ)*base73 + (1132192453768547/400000000000000000000000000000 : ℝ)*base76 + (146483186968547/400000000000000000000000000000 : ℝ)*base78 + (207962453768547/400000000000000000000000000000 : ℝ)*base80 + (1307311208831453/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3217811/2000000000000000000000 : ℝ)*base89 + (3217811/2000000000000000000000 : ℝ)*base91 + (3217811/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (156857899596969880074207/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18056011/20000000000000 : ℝ)*(base1) + (1908009/97656250000 : ℝ)*(base19) + (121778723/6250000000000 : ℝ)*(base23) + (106277621/50000000000000 : ℝ)*(upper3) + (23145063/10000000000000 : ℝ)*(upper5) + (125328147250867/20000000000000 : ℝ)*(major0) + (125328147250867/20000000000000 : ℝ)*(major1) + (125328147250867/20000000000000 : ℝ)*(major2) + (799875193/20000000000000 : ℝ)*(sp1) + (2010578439/50000000000000 : ℝ)*(sp2) + (208935119687359/25000000000000 : ℝ)*(sp4) + (4178672176461/500000000000 : ℝ)*(sp5) + (167146883770587/20000000000000 : ℝ)*(sp6) + (208770366164697/50000000000000 : ℝ)*(sp7) + (417540822609449/100000000000000 : ℝ)*(f.failure) + (417870194234691/50000000000000 : ℝ)*(f.sum) + (107441475693977/40000000000000000000000000000 : ℝ)*base66 + (323168079293977/80000000000000000000000000000 : ℝ)*base68 + (201054532573977/80000000000000000000000000000 : ℝ)*base70 + (57357257693977/80000000000000000000000000000 : ℝ)*base72 + (278602697693977/40000000000000000000000000000 : ℝ)*base74 + (27336950013977/80000000000000000000000000000 : ℝ)*base76 + (133482152733977/80000000000000000000000000000 : ℝ)*base78 + (35552928013977/80000000000000000000000000000 : ℝ)*base80 + (261661949733977/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (14933567/2000000000000000000000 : ℝ)*base89 + (14933567/2000000000000000000000 : ℝ)*base91 + (14933567/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1173_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (27/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27697/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1173_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1173_s1_0 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1042227461/5000000000 : ℝ)*x 0 + (2846657009/5000000000 : ℝ)*x 1 + (5008682029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042227461/5000000000 : ℝ)^4183 ≤ (10030711229/80000000000 : ℝ)^3159 := by
    have hnat : (1042227461 : ℕ)^4183*80000000000^3159 ≤ 10030711229^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042227461 5000000000 10030711229 80000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2846657009/5000000000 : ℝ)^4183 ≤ (47431401983033/100000000000000 : ℝ)^3159 := by
    have hnat : (2846657009 : ℕ)^4183*100000000000000^3159 ≤ 47431401983033^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2846657009 5000000000 47431401983033 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5008682029/10000000000 : ℝ)^4183 ≤ (40030208962373/100000000000000 : ℝ)^3159 := by
    have hnat : (5008682029 : ℕ)^4183*100000000000000^3159 ≤ 40030208962373^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5008682029 10000000000 40030208962373 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1042227461/5000000000 : ℝ), (2846657009/5000000000 : ℝ), (5008682029/10000000000 : ℝ)] ![(10030711229/80000000000 : ℝ), (47431401983033/100000000000000 : ℝ), (40030208962373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1042227461/5000000000 : ℝ)|^4183 ≤ (10030711229/80000000000 : ℝ)^3159
        have hw : |(-1042227461/5000000000 : ℝ)|=(1042227461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2846657009/5000000000 : ℝ)|^4183 ≤ (47431401983033/100000000000000 : ℝ)^3159
        have hw : |(2846657009/5000000000 : ℝ)|=(2846657009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5008682029/10000000000 : ℝ)|^4183 ≤ (40030208962373/100000000000000 : ℝ)^3159
        have hw : |(5008682029/10000000000 : ℝ)|=(5008682029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s1_1 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (108348491/200000000 : ℝ)*x 0 + (-2453342673/10000000000 : ℝ)*x 1 + (313042567/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108348491/200000000 : ℝ)^4183 ≤ (11103016472159/25000000000000 : ℝ)^3159 := by
    have hnat : (108348491 : ℕ)^4183*25000000000000^3159 ≤ 11103016472159^3159*200000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108348491 200000000 11103016472159 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2453342673/10000000000 : ℝ)^4183 ≤ (7778867628969/50000000000000 : ℝ)^3159 := by
    have hnat : (2453342673 : ℕ)^4183*50000000000000^3159 ≤ 7778867628969^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2453342673 10000000000 7778867628969 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313042567/625000000 : ℝ)^4183 ≤ (20015099417293/50000000000000 : ℝ)^3159 := by
    have hnat : (313042567 : ℕ)^4183*50000000000000^3159 ≤ 20015099417293^3159*625000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313042567 625000000 20015099417293 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108348491/200000000 : ℝ), (-2453342673/10000000000 : ℝ), (313042567/625000000 : ℝ)] ![(11103016472159/25000000000000 : ℝ), (7778867628969/50000000000000 : ℝ), (20015099417293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108348491/200000000 : ℝ)|^4183 ≤ (11103016472159/25000000000000 : ℝ)^3159
        have hw : |(108348491/200000000 : ℝ)|=(108348491/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2453342673/10000000000 : ℝ)|^4183 ≤ (7778867628969/50000000000000 : ℝ)^3159
        have hw : |(-2453342673/10000000000 : ℝ)|=(2453342673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(313042567/625000000 : ℝ)|^4183 ≤ (20015099417293/50000000000000 : ℝ)^3159
        have hw : |(313042567/625000000 : ℝ)|=(313042567/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s1_2 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5417426661/10000000000 : ℝ)*x 0 + (2504339547/5000000000 : ℝ)*x 1 + (-613335609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417426661/10000000000 : ℝ)^4183 ≤ (22206044402207/50000000000000 : ℝ)^3159 := by
    have hnat : (5417426661 : ℕ)^4183*50000000000000^3159 ≤ 22206044402207^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417426661 10000000000 22206044402207 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2504339547/5000000000 : ℝ)^4183 ≤ (2501886118857/6250000000000 : ℝ)^3159 := by
    have hnat : (2504339547 : ℕ)^4183*6250000000000^3159 ≤ 2501886118857^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2504339547 5000000000 2501886118857 6250000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (613335609/2500000000 : ℝ)^4183 ≤ (7778866633919/50000000000000 : ℝ)^3159 := by
    have hnat : (613335609 : ℕ)^4183*50000000000000^3159 ≤ 7778866633919^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613335609 2500000000 7778866633919 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417426661/10000000000 : ℝ), (2504339547/5000000000 : ℝ), (-613335609/2500000000 : ℝ)] ![(22206044402207/50000000000000 : ℝ), (2501886118857/6250000000000 : ℝ), (7778866633919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417426661/10000000000 : ℝ)|^4183 ≤ (22206044402207/50000000000000 : ℝ)^3159
        have hw : |(5417426661/10000000000 : ℝ)|=(5417426661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2504339547/5000000000 : ℝ)|^4183 ≤ (2501886118857/6250000000000 : ℝ)^3159
        have hw : |(2504339547/5000000000 : ℝ)|=(2504339547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-613335609/2500000000 : ℝ)|^4183 ≤ (7778866633919/50000000000000 : ℝ)^3159
        have hw : |(-613335609/2500000000 : ℝ)|=(613335609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s1_3 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2157400159/5000000000 : ℝ)*x 0 + (3682807187/10000000000 : ℝ)*x 1 + (1010629253/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157400159/5000000000 : ℝ)^4183 ≤ (16428656343737/50000000000000 : ℝ)^3159 := by
    have hnat : (2157400159 : ℕ)^4183*50000000000000^3159 ≤ 16428656343737^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157400159 5000000000 16428656343737 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3682807187/10000000000 : ℝ)^4183 ≤ (26641244306461/100000000000000 : ℝ)^3159 := by
    have hnat : (3682807187 : ℕ)^4183*100000000000000^3159 ≤ 26641244306461^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3682807187 10000000000 26641244306461 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010629253/2000000000 : ℝ)^4183 ≤ (4050144299691/10000000000000 : ℝ)^3159 := by
    have hnat : (1010629253 : ℕ)^4183*10000000000000^3159 ≤ 4050144299691^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010629253 2000000000 4050144299691 10000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157400159/5000000000 : ℝ), (3682807187/10000000000 : ℝ), (1010629253/2000000000 : ℝ)] ![(16428656343737/50000000000000 : ℝ), (26641244306461/100000000000000 : ℝ), (4050144299691/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157400159/5000000000 : ℝ)|^4183 ≤ (16428656343737/50000000000000 : ℝ)^3159
        have hw : |(2157400159/5000000000 : ℝ)|=(2157400159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3682807187/10000000000 : ℝ)|^4183 ≤ (26641244306461/100000000000000 : ℝ)^3159
        have hw : |(3682807187/10000000000 : ℝ)|=(3682807187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010629253/2000000000 : ℝ)|^4183 ≤ (4050144299691/10000000000000 : ℝ)^3159
        have hw : |(1010629253/2000000000 : ℝ)|=(1010629253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s1_4 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2085222669/10000000000 : ℝ)*x 0 + (5017920089/10000000000 : ℝ)*x 1 + (5550676/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2085222669/10000000000 : ℝ)^4183 ≤ (2508900905989/20000000000000 : ℝ)^3159 := by
    have hnat : (2085222669 : ℕ)^4183*20000000000000^3159 ≤ 2508900905989^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085222669 10000000000 2508900905989 20000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5017920089/10000000000 : ℝ)^4183 ≤ (8025600635497/20000000000000 : ℝ)^3159 := by
    have hnat : (5017920089 : ℕ)^4183*20000000000000^3159 ≤ 8025600635497^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5017920089 10000000000 8025600635497 20000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5550676/9765625 : ℝ)^4183 ≤ (47327492275657/100000000000000 : ℝ)^3159 := by
    have hnat : (5550676 : ℕ)^4183*100000000000000^3159 ≤ 47327492275657^3159*9765625^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5550676 9765625 47327492275657 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2085222669/10000000000 : ℝ), (5017920089/10000000000 : ℝ), (5550676/9765625 : ℝ)] ![(2508900905989/20000000000000 : ℝ), (8025600635497/20000000000000 : ℝ), (47327492275657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2085222669/10000000000 : ℝ)|^4183 ≤ (2508900905989/20000000000000 : ℝ)^3159
        have hw : |(-2085222669/10000000000 : ℝ)|=(2085222669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5017920089/10000000000 : ℝ)|^4183 ≤ (8025600635497/20000000000000 : ℝ)^3159
        have hw : |(5017920089/10000000000 : ℝ)|=(5017920089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5550676/9765625 : ℝ)|^4183 ≤ (47327492275657/100000000000000 : ℝ)^3159
        have hw : |(5550676/9765625 : ℝ)|=(5550676/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s1_5 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2620813393/5000000000 : ℝ)*x 0 + (-1778128771/10000000000 : ℝ)*x 1 + (710486857/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620813393/5000000000 : ℝ)^4183 ≤ (8502763980819/20000000000000 : ℝ)^3159 := by
    have hnat : (2620813393 : ℕ)^4183*20000000000000^3159 ≤ 8502763980819^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620813393 5000000000 8502763980819 20000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1778128771/10000000000 : ℝ)^4183 ≤ (5079329395049/50000000000000 : ℝ)^3159 := by
    have hnat : (1778128771 : ℕ)^4183*50000000000000^3159 ≤ 5079329395049^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778128771 10000000000 5079329395049 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (710486857/1250000000 : ℝ)^4183 ≤ (11831880323821/25000000000000 : ℝ)^3159 := by
    have hnat : (710486857 : ℕ)^4183*25000000000000^3159 ≤ 11831880323821^3159*1250000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710486857 1250000000 11831880323821 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620813393/5000000000 : ℝ), (-1778128771/10000000000 : ℝ), (710486857/1250000000 : ℝ)] ![(8502763980819/20000000000000 : ℝ), (5079329395049/50000000000000 : ℝ), (11831880323821/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620813393/5000000000 : ℝ)|^4183 ≤ (8502763980819/20000000000000 : ℝ)^3159
        have hw : |(2620813393/5000000000 : ℝ)|=(2620813393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1778128771/10000000000 : ℝ)|^4183 ≤ (5079329395049/50000000000000 : ℝ)^3159
        have hw : |(-1778128771/10000000000 : ℝ)|=(1778128771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(710486857/1250000000 : ℝ)|^4183 ≤ (11831880323821/25000000000000 : ℝ)^3159
        have hw : |(710486857/1250000000 : ℝ)|=(710486857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s1_6 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524162617/1000000000 : ℝ)*x 0 + (5683896021/10000000000 : ℝ)*x 1 + (-1778127947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524162617/1000000000 : ℝ)^4183 ≤ (8502762657657/20000000000000 : ℝ)^3159 := by
    have hnat : (524162617 : ℕ)^4183*20000000000000^3159 ≤ 8502762657657^3159*1000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524162617 1000000000 8502762657657 20000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5683896021/10000000000 : ℝ)^4183 ≤ (23663767070109/50000000000000 : ℝ)^3159 := by
    have hnat : (5683896021 : ℕ)^4183*50000000000000^3159 ≤ 23663767070109^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5683896021 10000000000 23663767070109 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1778127947/10000000000 : ℝ)^4183 ≤ (10158652556503/100000000000000 : ℝ)^3159 := by
    have hnat : (1778127947 : ℕ)^4183*100000000000000^3159 ≤ 10158652556503^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778127947 10000000000 10158652556503 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524162617/1000000000 : ℝ), (5683896021/10000000000 : ℝ), (-1778127947/10000000000 : ℝ)] ![(8502762657657/20000000000000 : ℝ), (23663767070109/50000000000000 : ℝ), (10158652556503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524162617/1000000000 : ℝ)|^4183 ≤ (8502762657657/20000000000000 : ℝ)^3159
        have hw : |(524162617/1000000000 : ℝ)|=(524162617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5683896021/10000000000 : ℝ)|^4183 ≤ (23663767070109/50000000000000 : ℝ)^3159
        have hw : |(5683896021/10000000000 : ℝ)|=(5683896021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1778127947/10000000000 : ℝ)|^4183 ≤ (10158652556503/100000000000000 : ℝ)^3159
        have hw : |(-1778127947/10000000000 : ℝ)|=(1778127947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s1_7 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (863265091/2000000000 : ℝ)*x 0 + (5034658767/10000000000 : ℝ)*x 1 + (462707209/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863265091/2000000000 : ℝ)^4183 ≤ (32872692226273/100000000000000 : ℝ)^3159 := by
    have hnat : (863265091 : ℕ)^4183*100000000000000^3159 ≤ 32872692226273^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863265091 2000000000 32872692226273 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5034658767/10000000000 : ℝ)^4183 ≤ (40305347693979/100000000000000 : ℝ)^3159 := by
    have hnat : (5034658767 : ℕ)^4183*100000000000000^3159 ≤ 40305347693979^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5034658767 10000000000 40305347693979 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (462707209/1250000000 : ℝ)^4183 ≤ (13410980030099/50000000000000 : ℝ)^3159 := by
    have hnat : (462707209 : ℕ)^4183*50000000000000^3159 ≤ 13410980030099^3159*1250000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462707209 1250000000 13410980030099 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863265091/2000000000 : ℝ), (5034658767/10000000000 : ℝ), (462707209/1250000000 : ℝ)] ![(32872692226273/100000000000000 : ℝ), (40305347693979/100000000000000 : ℝ), (13410980030099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863265091/2000000000 : ℝ)|^4183 ≤ (32872692226273/100000000000000 : ℝ)^3159
        have hw : |(863265091/2000000000 : ℝ)|=(863265091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5034658767/10000000000 : ℝ)|^4183 ≤ (40305347693979/100000000000000 : ℝ)^3159
        have hw : |(5034658767/10000000000 : ℝ)|=(5034658767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(462707209/1250000000 : ℝ)|^4183 ≤ (13410980030099/50000000000000 : ℝ)^3159
        have hw : |(462707209/1250000000 : ℝ)|=(462707209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s1_8 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522579/1000000000 : ℝ)*x 0 + (5490593109/10000000000 : ℝ)*x 1 + (793527269/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522579/1000000000 : ℝ)^4183 ≤ (4511597679/100000000000000 : ℝ)^3159 := by
    have hnat : (522579 : ℕ)^4183*100000000000000^3159 ≤ 4511597679^3159*1000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522579 1000000000 4511597679 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490593109/10000000000 : ℝ)^4183 ≤ (2825504639487/6250000000000 : ℝ)^3159 := by
    have hnat : (5490593109 : ℕ)^4183*6250000000000^3159 ≤ 2825504639487^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490593109 10000000000 2825504639487 6250000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (793527269/1250000000 : ℝ)^4183 ≤ (54787414162623/100000000000000 : ℝ)^3159 := by
    have hnat : (793527269 : ℕ)^4183*100000000000000^3159 ≤ 54787414162623^3159*1250000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793527269 1250000000 54787414162623 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522579/1000000000 : ℝ), (5490593109/10000000000 : ℝ), (793527269/1250000000 : ℝ)] ![(4511597679/100000000000000 : ℝ), (2825504639487/6250000000000 : ℝ), (54787414162623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522579/1000000000 : ℝ)|^4183 ≤ (4511597679/100000000000000 : ℝ)^3159
        have hw : |(522579/1000000000 : ℝ)|=(522579/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490593109/10000000000 : ℝ)|^4183 ≤ (2825504639487/6250000000000 : ℝ)^3159
        have hw : |(5490593109/10000000000 : ℝ)|=(5490593109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(793527269/1250000000 : ℝ)|^4183 ≤ (54787414162623/100000000000000 : ℝ)^3159
        have hw : |(793527269/1250000000 : ℝ)|=(793527269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s1_9 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (986258959/10000000000 : ℝ)*x 0 + (-4389451063/10000000000 : ℝ)*x 1 + (3473519127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (986258959/10000000000 : ℝ)^4183 ≤ (2327340372873/50000000000000 : ℝ)^3159 := by
    have hnat : (986258959 : ℕ)^4183*50000000000000^3159 ≤ 2327340372873^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986258959 10000000000 2327340372873 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4389451063/10000000000 : ℝ)^4183 ≤ (672243061399/2000000000000 : ℝ)^3159 := by
    have hnat : (4389451063 : ℕ)^4183*2000000000000^3159 ≤ 672243061399^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4389451063 10000000000 672243061399 2000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3473519127/5000000000 : ℝ)^4183 ≤ (15433291543189/25000000000000 : ℝ)^3159 := by
    have hnat : (3473519127 : ℕ)^4183*25000000000000^3159 ≤ 15433291543189^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3473519127 5000000000 15433291543189 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(986258959/10000000000 : ℝ), (-4389451063/10000000000 : ℝ), (3473519127/5000000000 : ℝ)] ![(2327340372873/50000000000000 : ℝ), (672243061399/2000000000000 : ℝ), (15433291543189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(986258959/10000000000 : ℝ)|^4183 ≤ (2327340372873/50000000000000 : ℝ)^3159
        have hw : |(986258959/10000000000 : ℝ)|=(986258959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4389451063/10000000000 : ℝ)|^4183 ≤ (672243061399/2000000000000 : ℝ)^3159
        have hw : |(-4389451063/10000000000 : ℝ)|=(4389451063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3473519127/5000000000 : ℝ)|^4183 ≤ (15433291543189/25000000000000 : ℝ)^3159
        have hw : |(3473519127/5000000000 : ℝ)|=(3473519127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s1_10 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (493126467/5000000000 : ℝ)*x 0 + (1736755833/2500000000 : ℝ)*x 1 + (-1097368023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (493126467/5000000000 : ℝ)^4183 ≤ (18182199583/390625000000 : ℝ)^3159 := by
    have hnat : (493126467 : ℕ)^4183*390625000000^3159 ≤ 18182199583^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493126467 5000000000 18182199583 390625000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1736755833/2500000000 : ℝ)^4183 ≤ (30866495294571/50000000000000 : ℝ)^3159 := by
    have hnat : (1736755833 : ℕ)^4183*50000000000000^3159 ≤ 30866495294571^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736755833 2500000000 30866495294571 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097368023/2500000000 : ℝ)^4183 ≤ (33612366297501/100000000000000 : ℝ)^3159 := by
    have hnat : (1097368023 : ℕ)^4183*100000000000000^3159 ≤ 33612366297501^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097368023 2500000000 33612366297501 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(493126467/5000000000 : ℝ), (1736755833/2500000000 : ℝ), (-1097368023/2500000000 : ℝ)] ![(18182199583/390625000000 : ℝ), (30866495294571/50000000000000 : ℝ), (33612366297501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(493126467/5000000000 : ℝ)|^4183 ≤ (18182199583/390625000000 : ℝ)^3159
        have hw : |(493126467/5000000000 : ℝ)|=(493126467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1736755833/2500000000 : ℝ)|^4183 ≤ (30866495294571/50000000000000 : ℝ)^3159
        have hw : |(1736755833/2500000000 : ℝ)|=(1736755833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097368023/2500000000 : ℝ)|^4183 ≤ (33612366297501/100000000000000 : ℝ)^3159
        have hw : |(-1097368023/2500000000 : ℝ)|=(1097368023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s1_11 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1912312441/10000000000 : ℝ)*x 0 + (580442887/1000000000 : ℝ)*x 1 + (200811169/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1912312441/10000000000 : ℝ)^4183 ≤ (11185974976037/100000000000000 : ℝ)^3159 := by
    have hnat : (1912312441 : ℕ)^4183*100000000000000^3159 ≤ 11185974976037^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912312441 10000000000 11185974976037 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (580442887/1000000000 : ℝ)^4183 ≤ (48661038624819/100000000000000 : ℝ)^3159 := by
    have hnat : (580442887 : ℕ)^4183*100000000000000^3159 ≤ 48661038624819^3159*1000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580442887 1000000000 48661038624819 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200811169/400000000 : ℝ)^4183 ≤ (20076493190133/50000000000000 : ℝ)^3159 := by
    have hnat : (200811169 : ℕ)^4183*50000000000000^3159 ≤ 20076493190133^3159*400000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200811169 400000000 20076493190133 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1912312441/10000000000 : ℝ), (580442887/1000000000 : ℝ), (200811169/400000000 : ℝ)] ![(11185974976037/100000000000000 : ℝ), (48661038624819/100000000000000 : ℝ), (20076493190133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1912312441/10000000000 : ℝ)|^4183 ≤ (11185974976037/100000000000000 : ℝ)^3159
        have hw : |(1912312441/10000000000 : ℝ)|=(1912312441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(580442887/1000000000 : ℝ)|^4183 ≤ (48661038624819/100000000000000 : ℝ)^3159
        have hw : |(580442887/1000000000 : ℝ)|=(580442887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200811169/400000000 : ℝ)|^4183 ≤ (20076493190133/50000000000000 : ℝ)^3159
        have hw : |(200811169/400000000 : ℝ)|=(200811169/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1173_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (27/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (5821/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10149/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27697/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (27/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27697/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (27/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27697/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (27/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27697/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (27/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27697/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (27/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27697/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (27/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (27/5000 : ℝ) ^ (8365/2048 : ℝ) ≤ (54704659207/100000000000000000000 : ℝ) := by
    have hpowers : (27/5000 : ℝ)^8365 ≤ (54704659207/100000000000000000000 : ℝ)^2048 := by
      have hnat : (27 : ℕ)^8365*100000000000000000000^2048 ≤ 54704659207^2048*5000^8365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27 5000 54704659207 100000000000000000000 8365 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27/5000 : ℝ)) (X := (54704659207/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27697/100000 : ℝ) ^ (8365/2048 : ℝ) ≤ (527997341459364203/100000000000000000000 : ℝ) := by
    have hpowers : (27697/100000 : ℝ)^8365 ≤ (527997341459364203/100000000000000000000 : ℝ)^2048 := by
      have hnat : (27697 : ℕ)^8365*100000000000000000000^2048 ≤ 527997341459364203^2048*100000^8365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27697 100000 527997341459364203 100000000000000000000 8365 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27697/100000 : ℝ)) (X := (527997341459364203/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000054704659207/50000000000000000000 : ℝ) ≤ (2000000000535733/2000000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (50000000054704659207/50000000000000000000 : ℝ)^2048 ≤ (2000000000535733/2000000000000000 : ℝ)^8365 := by
      have hnat : (50000000054704659207 : ℕ)^2048*2000000000000000^8365 ≤ 2000000000535733^8365*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000054704659207 50000000000000000000 2000000000535733 2000000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000000535733/2000000000000000 : ℝ)) (X := (50000000054704659207/50000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10052799739616402341/10000000000000000000 : ℝ) ≤ (2503225312321449/2500000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (10052799739616402341/10000000000000000000 : ℝ)^2048 ≤ (2503225312321449/2500000000000000 : ℝ)^8365 := by
      have hnat : (10052799739616402341 : ℕ)^2048*2500000000000000^8365 ≤ 2503225312321449^8365*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10052799739616402341 10000000000000000000 2503225312321449 2500000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503225312321449/2500000000000000 : ℝ)) (X := (10052799739616402341/10000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50527997341459364203/50000000000000000000 : ℝ) ≤ (10025802495892927/10000000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (50527997341459364203/50000000000000000000 : ℝ)^2048 ≤ (10025802495892927/10000000000000000 : ℝ)^8365 := by
      have hnat : (50527997341459364203 : ℕ)^2048*10000000000000000^8365 ≤ 10025802495892927^8365*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50527997341459364203 50000000000000000000 10025802495892927 10000000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10025802495892927/10000000000000000 : ℝ)) (X := (50527997341459364203/50000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(54704659207/100000000000000000000 : ℝ) ≤ ((10862242669056352157/10862800000000000000 : ℝ)+2*(12901246607131/2715700000000000 : ℝ)*(27/5000 : ℝ))^(8365/2048 : ℝ) := by
    rw [show (10862242669056352157/10862800000000000000 : ℝ)+2*(12901246607131/2715700000000000 : ℝ)*(27/5000 : ℝ)=(2000000000535733/2000000000000000 : ℝ) by norm_num, show 1+2*(54704659207/100000000000000000000 : ℝ)=(50000000054704659207/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(527997341459364203/100000000000000000000 : ℝ)+(54704659207/100000000000000000000 : ℝ) ≤ ((10862242669056352157/10862800000000000000 : ℝ)+(12901246607131/2715700000000000 : ℝ)*((27697/100000 : ℝ)+(27/5000 : ℝ)))^(8365/2048 : ℝ) := by
    rw [show (10862242669056352157/10862800000000000000 : ℝ)+(12901246607131/2715700000000000 : ℝ)*((27697/100000 : ℝ)+(27/5000 : ℝ))=(2503225312321449/2500000000000000 : ℝ) by norm_num, show 1+(527997341459364203/100000000000000000000 : ℝ)+(54704659207/100000000000000000000 : ℝ)=(10052799739616402341/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(527997341459364203/100000000000000000000 : ℝ) ≤ ((10862242669056352157/10862800000000000000 : ℝ)+2*(12901246607131/2715700000000000 : ℝ)*(27697/100000 : ℝ))^(8365/2048 : ℝ) := by
    rw [show (10862242669056352157/10862800000000000000 : ℝ)+2*(12901246607131/2715700000000000 : ℝ)*(27697/100000 : ℝ)=(10025802495892927/10000000000000000 : ℝ) by norm_num, show 1+2*(527997341459364203/100000000000000000000 : ℝ)=(50527997341459364203/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10862242669056352157/10862800000000000000 : ℝ)*(X 1 0+X 2 0)+(12901246607131/2715700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (27/5000 : ℝ)) (hi := (27697/100000 : ℝ)) (c := (10862242669056352157/10862800000000000000 : ℝ)) (alpha := (12901246607131/2715700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10862242669056352157/10862800000000000000 : ℝ)*(X 0 1+X 2 1)+(12901246607131/2715700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (27/5000 : ℝ)) (hi := (27697/100000 : ℝ)) (c := (10862242669056352157/10862800000000000000 : ℝ)) (alpha := (12901246607131/2715700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10862242669056352157/10862800000000000000 : ℝ)*(X 0 2+X 1 2)+(12901246607131/2715700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (27/5000 : ℝ)) (hi := (27697/100000 : ℝ)) (c := (10862242669056352157/10862800000000000000 : ℝ)) (alpha := (12901246607131/2715700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1042227461/5000000000 : ℝ)*X 0 0+(2846657009/5000000000 : ℝ)*X 0 1+(5008682029/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((108348491/200000000 : ℝ)*X 1 0+(-2453342673/10000000000 : ℝ)*X 1 1+(313042567/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5417426661/10000000000 : ℝ)*X 2 0+(2504339547/5000000000 : ℝ)*X 2 1+(-613335609/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2157400159/5000000000 : ℝ)*X 0 0+(3682807187/10000000000 : ℝ)*X 0 1+(1010629253/2000000000 : ℝ)*X 0 2+(2157400159/5000000000 : ℝ)*X 1 0+(3682807187/10000000000 : ℝ)*X 1 1+(1010629253/2000000000 : ℝ)*X 1 2+(2157400159/5000000000 : ℝ)*X 2 0+(3682807187/10000000000 : ℝ)*X 2 1+(1010629253/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2085222669/10000000000 : ℝ)*X 0 0+(5017920089/10000000000 : ℝ)*X 0 1+(5550676/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2620813393/5000000000 : ℝ)*X 1 0+(-1778128771/10000000000 : ℝ)*X 1 1+(710486857/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((524162617/1000000000 : ℝ)*X 2 0+(5683896021/10000000000 : ℝ)*X 2 1+(-1778127947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863265091/2000000000 : ℝ)*X 0 0+(5034658767/10000000000 : ℝ)*X 0 1+(462707209/1250000000 : ℝ)*X 0 2+(863265091/2000000000 : ℝ)*X 1 0+(5034658767/10000000000 : ℝ)*X 1 1+(462707209/1250000000 : ℝ)*X 1 2+(863265091/2000000000 : ℝ)*X 2 0+(5034658767/10000000000 : ℝ)*X 2 1+(462707209/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((522579/1000000000 : ℝ)*X 0 0+(5490593109/10000000000 : ℝ)*X 0 1+(793527269/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((986258959/10000000000 : ℝ)*X 1 0+(-4389451063/10000000000 : ℝ)*X 1 1+(3473519127/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((493126467/5000000000 : ℝ)*X 2 0+(1736755833/2500000000 : ℝ)*X 2 1+(-1097368023/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1912312441/10000000000 : ℝ)*X 0 0+(580442887/1000000000 : ℝ)*X 0 1+(200811169/400000000 : ℝ)*X 0 2+(1912312441/10000000000 : ℝ)*X 1 0+(580442887/1000000000 : ℝ)*X 1 1+(200811169/400000000 : ℝ)*X 1 2+(1912312441/10000000000 : ℝ)*X 2 0+(580442887/1000000000 : ℝ)*X 2 1+(200811169/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77715861417667075076509167/8356000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4192481/2000000000000 : ℝ)*(lower2) + (219039540758567/20000000000000 : ℝ)*(major0) + (219039540758567/20000000000000 : ℝ)*(major1) + (219039540758567/20000000000000 : ℝ)*(major2) + (730320962914323/50000000000000 : ℝ)*(sp0) + (1460641603267253/100000000000000 : ℝ)*(sp1) + (730319790189907/50000000000000 : ℝ)*(sp2) + (729746320539123/100000000000000 : ℝ)*(sp3) + (2644784539/50000000000000 : ℝ)*(sp4) + (2338967633/50000000000000 : ℝ)*(sp5) + (6552412501/100000000000000 : ℝ)*(sp6) + (233548801/25000000000000 : ℝ)*(sp9) + (1082605409/100000000000000 : ℝ)*(sp10) + (780814313/50000000000000 : ℝ)*(sp11) + (182436970541937/25000000000000 : ℝ)*(f.failure) + (1460647215397723/100000000000000 : ℝ)*(f.sum) + (3579771115787/1086280000000000000000000000 : ℝ)*base65 + (1615761630376108981/217256000000000000000000000000000 : ℝ)*base68 + (1310841848033868981/217256000000000000000000000000000 : ℝ)*base70 + (370239250428964981/217256000000000000000000000000000 : ℝ)*base72 + (113179228575721/27157000000000000000000000000 : ℝ)*base74 + (563396157089500981/217256000000000000000000000000000 : ℝ)*base76 + (432018898307172981/217256000000000000000000000000000 : ℝ)*base78 + (1579089307488388981/217256000000000000000000000000000 : ℝ)*base80 + (10376307173577/5431400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1608329/500000000000000000000 : ℝ)*base90 + (1608329/500000000000000000000 : ℝ)*base92 + (1608329/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (238722708566473496896426431/54314000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112587675910761/10000000000000 : ℝ)*(major0) + (112587675910761/10000000000000 : ℝ)*(major1) + (112587675910761/10000000000000 : ℝ)*(major2) + (15490021/400000000000 : ℝ)*(sp1) + (387805547/6250000000000 : ℝ)*(sp2) + (307902749/25000000000000 : ℝ)*(sp3) + (93847557738561/6250000000000 : ℝ)*(sp4) + (750779675274091/50000000000000 : ℝ)*(sp5) + (750778569584687/50000000000000 : ℝ)*(sp6) + (93773447732899/12500000000000 : ℝ)*(sp7) + (523337783/20000000000000 : ℝ)*(sp8) + (158726229/50000000000000 : ℝ)*(sp9) + (39289553/20000000000000 : ℝ)*(sp10) + (1017727357/100000000000000 : ℝ)*(sp11) + (150037966240309/20000000000000 : ℝ)*(f.failure) + (150156354050589/10000000000000 : ℝ)*(f.sum) + (8113731173343/5431400000000000000000000000 : ℝ)*base65 + (248173127602114523/108628000000000000000000000000000 : ℝ)*base68 + (361062635326978523/108628000000000000000000000000000 : ℝ)*base70 + (358425981936853477/108628000000000000000000000000000 : ℝ)*base71 + (9065740695311/13578500000000000000000000000 : ℝ)*base73 + (261144598665261477/108628000000000000000000000000000 : ℝ)*base75 + (118012666230810523/108628000000000000000000000000000 : ℝ)*base78 + (281928944353758523/108628000000000000000000000000000 : ℝ)*base80 + (14903900533481/27157000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (796947/400000000000000000000 : ℝ)*base89 + (796947/400000000000000000000 : ℝ)*base91 + (796947/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1173_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (27/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5821/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10149/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1173_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1173_s2_0 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-427208927/2000000000 : ℝ)*x 0 + (2752504373/5000000000 : ℝ)*x 1 + (80689879/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427208927/2000000000 : ℝ)^4183 ≤ (12950941924519/100000000000000 : ℝ)^3159 := by
    have hnat : (427208927 : ℕ)^4183*100000000000000^3159 ≤ 12950941924519^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427208927 2000000000 12950941924519 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2752504373/5000000000 : ℝ)^4183 ≤ (4536531077307/10000000000000 : ℝ)^3159 := by
    have hnat : (2752504373 : ℕ)^4183*10000000000000^3159 ≤ 4536531077307^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752504373 5000000000 4536531077307 10000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80689879/156250000 : ℝ)^4183 ≤ (41683747288397/100000000000000 : ℝ)^3159 := by
    have hnat : (80689879 : ℕ)^4183*100000000000000^3159 ≤ 41683747288397^3159*156250000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80689879 156250000 41683747288397 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427208927/2000000000 : ℝ), (2752504373/5000000000 : ℝ), (80689879/156250000 : ℝ)] ![(12950941924519/100000000000000 : ℝ), (4536531077307/10000000000000 : ℝ), (41683747288397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427208927/2000000000 : ℝ)|^4183 ≤ (12950941924519/100000000000000 : ℝ)^3159
        have hw : |(-427208927/2000000000 : ℝ)|=(427208927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2752504373/5000000000 : ℝ)|^4183 ≤ (4536531077307/10000000000000 : ℝ)^3159
        have hw : |(2752504373/5000000000 : ℝ)|=(2752504373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80689879/156250000 : ℝ)|^4183 ≤ (41683747288397/100000000000000 : ℝ)^3159
        have hw : |(80689879/156250000 : ℝ)|=(80689879/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s2_1 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372542517/10000000000 : ℝ)*x 0 + (-1156522481/5000000000 : ℝ)*x 1 + (1291038807/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372542517/10000000000 : ℝ)^4183 ≤ (10981377082851/25000000000000 : ℝ)^3159 := by
    have hnat : (5372542517 : ℕ)^4183*25000000000000^3159 ≤ 10981377082851^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372542517 10000000000 10981377082851 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1156522481/5000000000 : ℝ)^4183 ≤ (1798839074759/12500000000000 : ℝ)^3159 := by
    have hnat : (1156522481 : ℕ)^4183*12500000000000^3159 ≤ 1798839074759^3159*5000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156522481 5000000000 1798839074759 12500000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291038807/2500000000 : ℝ)^4183 ≤ (5210472381729/12500000000000 : ℝ)^3159 := by
    have hnat : (1291038807 : ℕ)^4183*12500000000000^3159 ≤ 5210472381729^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291038807 2500000000 5210472381729 12500000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372542517/10000000000 : ℝ), (-1156522481/5000000000 : ℝ), (1291038807/2500000000 : ℝ)] ![(10981377082851/25000000000000 : ℝ), (1798839074759/12500000000000 : ℝ), (5210472381729/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372542517/10000000000 : ℝ)|^4183 ≤ (10981377082851/25000000000000 : ℝ)^3159
        have hw : |(5372542517/10000000000 : ℝ)|=(5372542517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1156522481/5000000000 : ℝ)|^4183 ≤ (1798839074759/12500000000000 : ℝ)^3159
        have hw : |(-1156522481/5000000000 : ℝ)|=(1156522481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1291038807/2500000000 : ℝ)|^4183 ≤ (5210472381729/12500000000000 : ℝ)^3159
        have hw : |(1291038807/2500000000 : ℝ)|=(1291038807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s2_2 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074508643/2000000000 : ℝ)*x 0 + (5164154119/10000000000 : ℝ)*x 1 + (-578261371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074508643/2000000000 : ℝ)^4183 ≤ (43925515888077/100000000000000 : ℝ)^3159 := by
    have hnat : (1074508643 : ℕ)^4183*100000000000000^3159 ≤ 43925515888077^3159*2000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074508643 2000000000 43925515888077 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5164154119/10000000000 : ℝ)^4183 ≤ (20841883600289/50000000000000 : ℝ)^3159 := by
    have hnat : (5164154119 : ℕ)^4183*50000000000000^3159 ≤ 20841883600289^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5164154119 10000000000 20841883600289 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (578261371/2500000000 : ℝ)^4183 ≤ (14390716898453/100000000000000 : ℝ)^3159 := by
    have hnat : (578261371 : ℕ)^4183*100000000000000^3159 ≤ 14390716898453^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578261371 2500000000 14390716898453 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074508643/2000000000 : ℝ), (5164154119/10000000000 : ℝ), (-578261371/2500000000 : ℝ)] ![(43925515888077/100000000000000 : ℝ), (20841883600289/50000000000000 : ℝ), (14390716898453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074508643/2000000000 : ℝ)|^4183 ≤ (43925515888077/100000000000000 : ℝ)^3159
        have hw : |(1074508643/2000000000 : ℝ)|=(1074508643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5164154119/10000000000 : ℝ)|^4183 ≤ (20841883600289/50000000000000 : ℝ)^3159
        have hw : |(5164154119/10000000000 : ℝ)|=(5164154119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-578261371/2500000000 : ℝ)|^4183 ≤ (14390716898453/100000000000000 : ℝ)^3159
        have hw : |(-578261371/2500000000 : ℝ)|=(578261371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s2_3 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4350266541/10000000000 : ℝ)*x 0 + (4022303433/10000000000 : ℝ)*x 1 + (18818199/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350266541/10000000000 : ℝ)^4183 ≤ (83038526193/250000000000 : ℝ)^3159 := by
    have hnat : (4350266541 : ℕ)^4183*250000000000^3159 ≤ 83038526193^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350266541 10000000000 83038526193 250000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4022303433/10000000000 : ℝ)^4183 ≤ (14970423253219/50000000000000 : ℝ)^3159 := by
    have hnat : (4022303433 : ℕ)^4183*50000000000000^3159 ≤ 14970423253219^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022303433 10000000000 14970423253219 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18818199/40000000 : ℝ)^4183 ≤ (36843742996273/100000000000000 : ℝ)^3159 := by
    have hnat : (18818199 : ℕ)^4183*100000000000000^3159 ≤ 36843742996273^3159*40000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18818199 40000000 36843742996273 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350266541/10000000000 : ℝ), (4022303433/10000000000 : ℝ), (18818199/40000000 : ℝ)] ![(83038526193/250000000000 : ℝ), (14970423253219/50000000000000 : ℝ), (36843742996273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350266541/10000000000 : ℝ)|^4183 ≤ (83038526193/250000000000 : ℝ)^3159
        have hw : |(4350266541/10000000000 : ℝ)|=(4350266541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4022303433/10000000000 : ℝ)|^4183 ≤ (14970423253219/50000000000000 : ℝ)^3159
        have hw : |(4022303433/10000000000 : ℝ)|=(4022303433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18818199/40000000 : ℝ)|^4183 ≤ (36843742996273/100000000000000 : ℝ)^3159
        have hw : |(18818199/40000000 : ℝ)|=(18818199/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s2_4 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-534034569/2500000000 : ℝ)*x 0 + (645806611/1250000000 : ℝ)*x 1 + (5502686073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534034569/2500000000 : ℝ)^4183 ≤ (1295169371773/10000000000000 : ℝ)^3159 := by
    have hnat : (534034569 : ℕ)^4183*10000000000000^3159 ≤ 1295169371773^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534034569 2500000000 1295169371773 10000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (645806611/1250000000 : ℝ)^4183 ≤ (41708338756967/100000000000000 : ℝ)^3159 := by
    have hnat : (645806611 : ℕ)^4183*100000000000000^3159 ≤ 41708338756967^3159*1250000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645806611 1250000000 41708338756967 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5502686073/10000000000 : ℝ)^4183 ≤ (45339967512733/100000000000000 : ℝ)^3159 := by
    have hnat : (5502686073 : ℕ)^4183*100000000000000^3159 ≤ 45339967512733^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502686073 10000000000 45339967512733 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534034569/2500000000 : ℝ), (645806611/1250000000 : ℝ), (5502686073/10000000000 : ℝ)] ![(1295169371773/10000000000000 : ℝ), (41708338756967/100000000000000 : ℝ), (45339967512733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534034569/2500000000 : ℝ)|^4183 ≤ (1295169371773/10000000000000 : ℝ)^3159
        have hw : |(-534034569/2500000000 : ℝ)|=(534034569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(645806611/1250000000 : ℝ)|^4183 ≤ (41708338756967/100000000000000 : ℝ)^3159
        have hw : |(645806611/1250000000 : ℝ)|=(645806611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5502686073/10000000000 : ℝ)|^4183 ≤ (45339967512733/100000000000000 : ℝ)^3159
        have hw : |(5502686073/10000000000 : ℝ)|=(5502686073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s2_5 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33036757/62500000 : ℝ)*x 0 + (-15796103/80000000 : ℝ)*x 1 + (5502686073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33036757/62500000 : ℝ)^4183 ≤ (1343429950031/3125000000000 : ℝ)^3159 := by
    have hnat : (33036757 : ℕ)^4183*3125000000000^3159 ≤ 1343429950031^3159*62500000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33036757 62500000 1343429950031 3125000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15796103/80000000 : ℝ)^4183 ≤ (11670274073939/100000000000000 : ℝ)^3159 := by
    have hnat : (15796103 : ℕ)^4183*100000000000000^3159 ≤ 11670274073939^3159*80000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15796103 80000000 11670274073939 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5502686073/10000000000 : ℝ)^4183 ≤ (45339967512733/100000000000000 : ℝ)^3159 := by
    have hnat : (5502686073 : ℕ)^4183*100000000000000^3159 ≤ 45339967512733^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502686073 10000000000 45339967512733 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33036757/62500000 : ℝ), (-15796103/80000000 : ℝ), (5502686073/10000000000 : ℝ)] ![(1343429950031/3125000000000 : ℝ), (11670274073939/100000000000000 : ℝ), (45339967512733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33036757/62500000 : ℝ)|^4183 ≤ (1343429950031/3125000000000 : ℝ)^3159
        have hw : |(33036757/62500000 : ℝ)|=(33036757/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15796103/80000000 : ℝ)|^4183 ≤ (11670274073939/100000000000000 : ℝ)^3159
        have hw : |(-15796103/80000000 : ℝ)|=(15796103/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5502686073/10000000000 : ℝ)|^4183 ≤ (45339967512733/100000000000000 : ℝ)^3159
        have hw : |(5502686073/10000000000 : ℝ)|=(5502686073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s2_6 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660735157/1250000000 : ℝ)*x 0 + (5502686071/10000000000 : ℝ)*x 1 + (-197451269/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660735157/1250000000 : ℝ)^4183 ≤ (10747439966403/25000000000000 : ℝ)^3159 := by
    have hnat : (660735157 : ℕ)^4183*25000000000000^3159 ≤ 10747439966403^3159*1250000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660735157 1250000000 10747439966403 25000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5502686071/10000000000 : ℝ)^4183 ≤ (1416873984091/3125000000000 : ℝ)^3159 := by
    have hnat : (5502686071 : ℕ)^4183*3125000000000^3159 ≤ 1416873984091^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502686071 10000000000 1416873984091 3125000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197451269/1000000000 : ℝ)^4183 ≤ (729392039129/6250000000000 : ℝ)^3159 := by
    have hnat : (197451269 : ℕ)^4183*6250000000000^3159 ≤ 729392039129^3159*1000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197451269 1000000000 729392039129 6250000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660735157/1250000000 : ℝ), (5502686071/10000000000 : ℝ), (-197451269/1000000000 : ℝ)] ![(10747439966403/25000000000000 : ℝ), (1416873984091/3125000000000 : ℝ), (729392039129/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660735157/1250000000 : ℝ)|^4183 ≤ (10747439966403/25000000000000 : ℝ)^3159
        have hw : |(660735157/1250000000 : ℝ)|=(660735157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5502686071/10000000000 : ℝ)|^4183 ≤ (1416873984091/3125000000000 : ℝ)^3159
        have hw : |(5502686071/10000000000 : ℝ)|=(5502686071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-197451269/1000000000 : ℝ)|^4183 ≤ (729392039129/6250000000000 : ℝ)^3159
        have hw : |(-197451269/1000000000 : ℝ)|=(197451269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1173_s2_7 (p : ℝ) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4350455669/10000000000 : ℝ)*x 0 + (4699947363/10000000000 : ℝ)*x 1 + (1006737491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350455669/10000000000 : ℝ)^4183 ≤ (33217322622479/100000000000000 : ℝ)^3159 := by
    have hnat : (4350455669 : ℕ)^4183*100000000000000^3159 ≤ 33217322622479^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350455669 10000000000 33217322622479 100000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4699947363/10000000000 : ℝ)^4183 ≤ (919900581127/2500000000000 : ℝ)^3159 := by
    have hnat : (4699947363 : ℕ)^4183*2500000000000^3159 ≤ 919900581127^3159*10000000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4699947363 10000000000 919900581127 2500000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006737491/2500000000 : ℝ)^4183 ≤ (14993327056829/50000000000000 : ℝ)^3159 := by
    have hnat : (1006737491 : ℕ)^4183*50000000000000^3159 ≤ 14993327056829^3159*2500000000^4183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006737491 2500000000 14993327056829 50000000000000 4183 3159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4183/1024 : ℝ)) 4183 3159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350455669/10000000000 : ℝ), (4699947363/10000000000 : ℝ), (1006737491/2500000000 : ℝ)] ![(33217322622479/100000000000000 : ℝ), (919900581127/2500000000000 : ℝ), (14993327056829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350455669/10000000000 : ℝ)|^4183 ≤ (33217322622479/100000000000000 : ℝ)^3159
        have hw : |(4350455669/10000000000 : ℝ)|=(4350455669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4699947363/10000000000 : ℝ)|^4183 ≤ (919900581127/2500000000000 : ℝ)^3159
        have hw : |(4699947363/10000000000 : ℝ)|=(4699947363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006737491/2500000000 : ℝ)|^4183 ≤ (14993327056829/50000000000000 : ℝ)^3159
        have hw : |(1006737491/2500000000 : ℝ)|=(1006737491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1173_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10149/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5821/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1151/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4103/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10149/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5821/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10149/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5821/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10149/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5821/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10149/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5821/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10149/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5821/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10149/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5821/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5821/100000 : ℝ) ^ (8365/2048 : ℝ) ≤ (112869467699101/12500000000000000000 : ℝ) := by
    have hpowers : (5821/100000 : ℝ)^8365 ≤ (112869467699101/12500000000000000000 : ℝ)^2048 := by
      have hnat : (5821 : ℕ)^8365*12500000000000000000^2048 ≤ 112869467699101^2048*100000^8365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5821 100000 112869467699101 12500000000000000000 8365 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5821/100000 : ℝ)) (X := (112869467699101/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10149/50000 : ℝ) ^ (8365/2048 : ℝ) ≤ (2967165185382743/2000000000000000000 : ℝ) := by
    have hpowers : (10149/50000 : ℝ)^8365 ≤ (2967165185382743/2000000000000000000 : ℝ)^2048 := by
      have hnat : (10149 : ℕ)^8365*2000000000000000000^2048 ≤ 2967165185382743^2048*50000^8365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10149 50000 2967165185382743 2000000000000000000 8365 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10149/50000 : ℝ)) (X := (2967165185382743/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250112869467699101/6250000000000000000 : ℝ) ≤ (1000004421376567/1000000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (6250112869467699101/6250000000000000000 : ℝ)^2048 ≤ (1000004421376567/1000000000000000 : ℝ)^8365 := by
      have hnat : (6250112869467699101 : ℕ)^2048*1000000000000000^8365 ≤ 1000004421376567^8365*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250112869467699101 6250000000000000000 1000004421376567 1000000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000004421376567/1000000000000000 : ℝ)) (X := (6250112869467699101/6250000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50074630607505364979/50000000000000000000 : ℝ) ≤ (2500913074826837/2500000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (50074630607505364979/50000000000000000000 : ℝ)^2048 ≤ (2500913074826837/2500000000000000 : ℝ)^8365 := by
      have hnat : (50074630607505364979 : ℕ)^2048*2500000000000000^8365 ≤ 2500913074826837^8365*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50074630607505364979 50000000000000000000 2500913074826837 2500000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500913074826837/2500000000000000 : ℝ)) (X := (50074630607505364979/50000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1002967165185382743/1000000000000000000 : ℝ) ≤ (5003630192424513/5000000000000000 : ℝ) ^ (8365/2048 : ℝ) := by
    have hpowers : (1002967165185382743/1000000000000000000 : ℝ)^2048 ≤ (5003630192424513/5000000000000000 : ℝ)^8365 := by
      have hnat : (1002967165185382743 : ℕ)^2048*5000000000000000^8365 ≤ 5003630192424513^8365*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1002967165185382743 1000000000000000000 5003630192424513 5000000000000000 2048 8365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003630192424513/5000000000000000 : ℝ)) (X := (1002967165185382743/1000000000000000000 : ℝ)) (by norm_num) 8365 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(112869467699101/12500000000000000000 : ℝ) ≤ ((72364317375404694657/72385000000000000000 : ℝ)+2*(1804042770839/723850000000000 : ℝ)*(5821/100000 : ℝ))^(8365/2048 : ℝ) := by
    rw [show (72364317375404694657/72385000000000000000 : ℝ)+2*(1804042770839/723850000000000 : ℝ)*(5821/100000 : ℝ)=(1000004421376567/1000000000000000 : ℝ) by norm_num, show 1+2*(112869467699101/12500000000000000000 : ℝ)=(6250112869467699101/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2967165185382743/2000000000000000000 : ℝ)+(112869467699101/12500000000000000000 : ℝ) ≤ ((72364317375404694657/72385000000000000000 : ℝ)+(1804042770839/723850000000000 : ℝ)*((10149/50000 : ℝ)+(5821/100000 : ℝ)))^(8365/2048 : ℝ) := by
    rw [show (72364317375404694657/72385000000000000000 : ℝ)+(1804042770839/723850000000000 : ℝ)*((10149/50000 : ℝ)+(5821/100000 : ℝ))=(2500913074826837/2500000000000000 : ℝ) by norm_num, show 1+(2967165185382743/2000000000000000000 : ℝ)+(112869467699101/12500000000000000000 : ℝ)=(50074630607505364979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2967165185382743/2000000000000000000 : ℝ) ≤ ((72364317375404694657/72385000000000000000 : ℝ)+2*(1804042770839/723850000000000 : ℝ)*(10149/50000 : ℝ))^(8365/2048 : ℝ) := by
    rw [show (72364317375404694657/72385000000000000000 : ℝ)+2*(1804042770839/723850000000000 : ℝ)*(10149/50000 : ℝ)=(5003630192424513/5000000000000000 : ℝ) by norm_num, show 1+2*(2967165185382743/2000000000000000000 : ℝ)=(1002967165185382743/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72364317375404694657/72385000000000000000 : ℝ)*(X 1 0+X 2 0)+(1804042770839/723850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (5821/100000 : ℝ)) (hi := (10149/50000 : ℝ)) (c := (72364317375404694657/72385000000000000000 : ℝ)) (alpha := (1804042770839/723850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72364317375404694657/72385000000000000000 : ℝ)*(X 0 1+X 2 1)+(1804042770839/723850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (5821/100000 : ℝ)) (hi := (10149/50000 : ℝ)) (c := (72364317375404694657/72385000000000000000 : ℝ)) (alpha := (1804042770839/723850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72364317375404694657/72385000000000000000 : ℝ)*(X 0 2+X 1 2)+(1804042770839/723850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8365/2048 : ℝ)) (lo := (5821/100000 : ℝ)) (hi := (10149/50000 : ℝ)) (c := (72364317375404694657/72385000000000000000 : ℝ)) (alpha := (1804042770839/723850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-427208927/2000000000 : ℝ)*X 0 0+(2752504373/5000000000 : ℝ)*X 0 1+(80689879/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5372542517/10000000000 : ℝ)*X 1 0+(-1156522481/5000000000 : ℝ)*X 1 1+(1291038807/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1074508643/2000000000 : ℝ)*X 2 0+(5164154119/10000000000 : ℝ)*X 2 1+(-578261371/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350266541/10000000000 : ℝ)*X 0 0+(4022303433/10000000000 : ℝ)*X 0 1+(18818199/40000000 : ℝ)*X 0 2+(4350266541/10000000000 : ℝ)*X 1 0+(4022303433/10000000000 : ℝ)*X 1 1+(18818199/40000000 : ℝ)*X 1 2+(4350266541/10000000000 : ℝ)*X 2 0+(4022303433/10000000000 : ℝ)*X 2 1+(18818199/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-534034569/2500000000 : ℝ)*X 0 0+(645806611/1250000000 : ℝ)*X 0 1+(5502686073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((33036757/62500000 : ℝ)*X 1 0+(-15796103/80000000 : ℝ)*X 1 1+(5502686073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660735157/1250000000 : ℝ)*X 2 0+(5502686071/10000000000 : ℝ)*X 2 1+(-197451269/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350455669/10000000000 : ℝ)*X 0 0+(4699947363/10000000000 : ℝ)*X 0 1+(1006737491/2500000000 : ℝ)*X 0 2+(4350455669/10000000000 : ℝ)*X 1 0+(4699947363/10000000000 : ℝ)*X 1 1+(1006737491/2500000000 : ℝ)*X 1 2+(4350455669/10000000000 : ℝ)*X 2 0+(4699947363/10000000000 : ℝ)*X 2 1+(1006737491/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1173_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7639536277587600964563733269/904812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (498947119/50000000000000 : ℝ)*(base19) + (545117049/50000000000000 : ℝ)*(base23) + (20505379/50000000000000 : ℝ)*(upper2) + (478030729/100000000000000 : ℝ)*(upper3) + (49045739/25000000000000 : ℝ)*(upper4) + (549951068554561/25000000000000 : ℝ)*(major0) + (549951068554561/25000000000000 : ℝ)*(major1) + (549951068554561/25000000000000 : ℝ)*(major2) + (1466908666444899/50000000000000 : ℝ)*(sp0) + (1466921112639389/50000000000000 : ℝ)*(sp1) + (1466921066469459/50000000000000 : ℝ)*(sp2) + (366438260542687/25000000000000 : ℝ)*(sp3) + (12945141609/50000000000000 : ℝ)*(sp4) + (600082593/5000000000000 : ℝ)*(sp7) + (91610315238913/6250000000000 : ℝ)*(f.failure) + (366730402896627/12500000000000 : ℝ)*(f.sum) + (108863692561959/36192500000000000000000000000 : ℝ)*base66 + (3613709212091080577/1809625000000000000000000000000000 : ℝ)*base67 + (7078194135663330577/1809625000000000000000000000000000 : ℝ)*base69 + (8484656415640330577/1809625000000000000000000000000000 : ℝ)*base71 + (50538537948587/18096250000000000000000000000 : ℝ)*base74 + (3258357732811580577/1809625000000000000000000000000000 : ℝ)*base75 + (432337988570669423/1809625000000000000000000000000000 : ℝ)*base78 + (4976393095277669423/1809625000000000000000000000000000 : ℝ)*base80 + (3511180354731/9048125000000000000000000000 : ℝ)*base82 + (763879/125000000000000000000 : ℝ)*base89 + (763879/125000000000000000000 : ℝ)*base91 + (763879/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (127030922801248677423/18680000000000000000000000 : ℝ) := by norm_num
    linear_combination (806082947/50000000000000 : ℝ)*(base19) + (346254851/20000000000000 : ℝ)*(base23) + (620599/100000000000000 : ℝ)*(upper2) + (19484371/10000000000000 : ℝ)*(upper3) + (145114319/100000000000000 : ℝ)*(upper5) + (223000830901749/10000000000000 : ℝ)*(major0) + (223000830901749/10000000000000 : ℝ)*(major1) + (223000830901749/10000000000000 : ℝ)*(major2) + (15661730997/100000000000000 : ℝ)*(sp1) + (4546900609/25000000000000 : ℝ)*(sp2) + (1487062956162657/50000000000000 : ℝ)*(sp4) + (2974108638428423/100000000000000 : ℝ)*(sp5) + (1487052996724311/50000000000000 : ℝ)*(sp6) + (742945239515321/50000000000000 : ℝ)*(sp7) + (742945239515321/50000000000000 : ℝ)*(f.failure) + (1487062956162657/50000000000000 : ℝ)*(f.sum) + (738644493777/233500000000000000000000000 : ℝ)*base66 + (13206319385905003/23350000000000000000000000000000 : ℝ)*base67 + (96002679776294997/23350000000000000000000000000000 : ℝ)*base70 + (28307258728755003/23350000000000000000000000000000 : ℝ)*base71 + (249991386811/93400000000000000000000000 : ℝ)*base73 + (76003481200844997/23350000000000000000000000000000 : ℝ)*base76 + (104127584537294997/23350000000000000000000000000000 : ℝ)*base78 + (227405881539005003/23350000000000000000000000000000 : ℝ)*base79 + (18284613469/29187500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (311343/1000000000000000000000 : ℝ)*base89 + (311343/1000000000000000000000 : ℝ)*base91 + (311343/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1173_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10149/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5821/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1151/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4103/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1173_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1173_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1151/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4103/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1173_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1173_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1173_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1151/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4103/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1173_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
