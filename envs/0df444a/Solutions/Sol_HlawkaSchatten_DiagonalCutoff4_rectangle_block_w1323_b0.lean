-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1323_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:43:43.118985+00:00
-- url     : https://prove2.me/submissions/209adb9d-3845-4341-9d30-dc203cc98222

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
theorem support_rectangle_w1323_s0_0 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1820431879/10000000000 : ℝ)*x 0 + (6005163489/10000000000 : ℝ)*x 1 + (4806355523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1820431879/10000000000 : ℝ)^4283 ≤ (5329496771663/50000000000000 : ℝ)^3259 := by
    have hnat : (1820431879 : ℕ)^4283*50000000000000^3259 ≤ 5329496771663^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820431879 10000000000 5329496771663 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6005163489/10000000000 : ℝ)^4283 ≤ (51160623671097/100000000000000 : ℝ)^3259 := by
    have hnat : (6005163489 : ℕ)^4283*100000000000000^3259 ≤ 51160623671097^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6005163489 10000000000 51160623671097 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4806355523/10000000000 : ℝ)^4283 ≤ (19090191384659/50000000000000 : ℝ)^3259 := by
    have hnat : (4806355523 : ℕ)^4283*50000000000000^3259 ≤ 19090191384659^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4806355523 10000000000 19090191384659 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1820431879/10000000000 : ℝ), (6005163489/10000000000 : ℝ), (4806355523/10000000000 : ℝ)] ![(5329496771663/50000000000000 : ℝ), (51160623671097/100000000000000 : ℝ), (19090191384659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1820431879/10000000000 : ℝ)|^4283 ≤ (5329496771663/50000000000000 : ℝ)^3259
        have hw : |(-1820431879/10000000000 : ℝ)|=(1820431879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6005163489/10000000000 : ℝ)|^4283 ≤ (51160623671097/100000000000000 : ℝ)^3259
        have hw : |(6005163489/10000000000 : ℝ)|=(6005163489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4806355523/10000000000 : ℝ)|^4283 ≤ (19090191384659/50000000000000 : ℝ)^3259
        have hw : |(4806355523/10000000000 : ℝ)|=(4806355523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s0_1 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2751970871/5000000000 : ℝ)*x 0 + (-1251387639/5000000000 : ℝ)*x 1 + (300397231/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2751970871/5000000000 : ℝ)^4283 ≤ (45623834029323/100000000000000 : ℝ)^3259 := by
    have hnat : (2751970871 : ℕ)^4283*100000000000000^3259 ≤ 45623834029323^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751970871 5000000000 45623834029323 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1251387639/5000000000 : ℝ)^4283 ≤ (16195781382179/100000000000000 : ℝ)^3259 := by
    have hnat : (1251387639 : ℕ)^4283*100000000000000^3259 ≤ 16195781382179^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251387639 5000000000 16195781382179 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300397231/625000000 : ℝ)^4283 ≤ (38180384575387/100000000000000 : ℝ)^3259 := by
    have hnat : (300397231 : ℕ)^4283*100000000000000^3259 ≤ 38180384575387^3259*625000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300397231 625000000 38180384575387 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2751970871/5000000000 : ℝ), (-1251387639/5000000000 : ℝ), (300397231/625000000 : ℝ)] ![(45623834029323/100000000000000 : ℝ), (16195781382179/100000000000000 : ℝ), (38180384575387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2751970871/5000000000 : ℝ)|^4283 ≤ (45623834029323/100000000000000 : ℝ)^3259
        have hw : |(2751970871/5000000000 : ℝ)|=(2751970871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1251387639/5000000000 : ℝ)|^4283 ≤ (16195781382179/100000000000000 : ℝ)^3259
        have hw : |(-1251387639/5000000000 : ℝ)|=(1251387639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(300397231/625000000 : ℝ)|^4283 ≤ (38180384575387/100000000000000 : ℝ)^3259
        have hw : |(300397231/625000000 : ℝ)|=(300397231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s0_2 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5503941027/10000000000 : ℝ)*x 0 + (4806356029/10000000000 : ℝ)*x 1 + (-500555157/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5503941027/10000000000 : ℝ)^4283 ≤ (5702978280027/12500000000000 : ℝ)^3259 := by
    have hnat : (5503941027 : ℕ)^4283*12500000000000^3259 ≤ 5702978280027^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503941027 10000000000 5702978280027 12500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4806356029/10000000000 : ℝ)^4283 ≤ (1193137126619/3125000000000 : ℝ)^3259 := by
    have hnat : (4806356029 : ℕ)^4283*3125000000000^3259 ≤ 1193137126619^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4806356029 10000000000 1193137126619 3125000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500555157/2000000000 : ℝ)^4283 ≤ (16195785693911/100000000000000 : ℝ)^3259 := by
    have hnat : (500555157 : ℕ)^4283*100000000000000^3259 ≤ 16195785693911^3259*2000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500555157 2000000000 16195785693911 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5503941027/10000000000 : ℝ), (4806356029/10000000000 : ℝ), (-500555157/2000000000 : ℝ)] ![(5702978280027/12500000000000 : ℝ), (1193137126619/3125000000000 : ℝ), (16195785693911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5503941027/10000000000 : ℝ)|^4283 ≤ (5702978280027/12500000000000 : ℝ)^3259
        have hw : |(5503941027/10000000000 : ℝ)|=(5503941027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4806356029/10000000000 : ℝ)|^4283 ≤ (1193137126619/3125000000000 : ℝ)^3259
        have hw : |(4806356029/10000000000 : ℝ)|=(4806356029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-500555157/2000000000 : ℝ)|^4283 ≤ (16195785693911/100000000000000 : ℝ)^3259
        have hw : |(-500555157/2000000000 : ℝ)|=(500555157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s0_3 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4181605107/10000000000 : ℝ)*x 0 + (1553781561/5000000000 : ℝ)*x 1 + (2800306737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4181605107/10000000000 : ℝ)^4283 ≤ (31795555300343/100000000000000 : ℝ)^3259 := by
    have hnat : (4181605107 : ℕ)^4283*100000000000000^3259 ≤ 31795555300343^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4181605107 10000000000 31795555300343 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1553781561/5000000000 : ℝ)^4283 ≤ (5381147062657/25000000000000 : ℝ)^3259 := by
    have hnat : (1553781561 : ℕ)^4283*25000000000000^3259 ≤ 5381147062657^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553781561 5000000000 5381147062657 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2800306737/5000000000 : ℝ)^4283 ≤ (46679856435993/100000000000000 : ℝ)^3259 := by
    have hnat : (2800306737 : ℕ)^4283*100000000000000^3259 ≤ 46679856435993^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2800306737 5000000000 46679856435993 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4181605107/10000000000 : ℝ), (1553781561/5000000000 : ℝ), (2800306737/5000000000 : ℝ)] ![(31795555300343/100000000000000 : ℝ), (5381147062657/25000000000000 : ℝ), (46679856435993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4181605107/10000000000 : ℝ)|^4283 ≤ (31795555300343/100000000000000 : ℝ)^3259
        have hw : |(4181605107/10000000000 : ℝ)|=(4181605107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1553781561/5000000000 : ℝ)|^4283 ≤ (5381147062657/25000000000000 : ℝ)^3259
        have hw : |(1553781561/5000000000 : ℝ)|=(1553781561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2800306737/5000000000 : ℝ)|^4283 ≤ (46679856435993/100000000000000 : ℝ)^3259
        have hw : |(2800306737/5000000000 : ℝ)|=(2800306737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s0_4 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1824989011/10000000000 : ℝ)*x 0 + (2418621871/5000000000 : ℝ)*x 1 + (5973173499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1824989011/10000000000 : ℝ)^4283 ≤ (1069407420351/10000000000000 : ℝ)^3259 := by
    have hnat : (1824989011 : ℕ)^4283*10000000000000^3259 ≤ 1069407420351^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824989011 10000000000 1069407420351 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2418621871/5000000000 : ℝ)^4283 ≤ (19251585830879/50000000000000 : ℝ)^3259 := by
    have hnat : (2418621871 : ℕ)^4283*50000000000000^3259 ≤ 19251585830879^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418621871 5000000000 19251585830879 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5973173499/10000000000 : ℝ)^4283 ≤ (50802754115009/100000000000000 : ℝ)^3259 := by
    have hnat : (5973173499 : ℕ)^4283*100000000000000^3259 ≤ 50802754115009^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5973173499 10000000000 50802754115009 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1824989011/10000000000 : ℝ), (2418621871/5000000000 : ℝ), (5973173499/10000000000 : ℝ)] ![(1069407420351/10000000000000 : ℝ), (19251585830879/50000000000000 : ℝ), (50802754115009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1824989011/10000000000 : ℝ)|^4283 ≤ (1069407420351/10000000000000 : ℝ)^3259
        have hw : |(-1824989011/10000000000 : ℝ)|=(1824989011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2418621871/5000000000 : ℝ)|^4283 ≤ (19251585830879/50000000000000 : ℝ)^3259
        have hw : |(2418621871/5000000000 : ℝ)|=(2418621871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5973173499/10000000000 : ℝ)|^4283 ≤ (50802754115009/100000000000000 : ℝ)^3259
        have hw : |(5973173499/10000000000 : ℝ)|=(5973173499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s0_5 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1035470653/2000000000 : ℝ)*x 0 + (-667979179/5000000000 : ℝ)*x 1 + (5973173421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035470653/2000000000 : ℝ)^4283 ≤ (21049826783857/50000000000000 : ℝ)^3259 := by
    have hnat : (1035470653 : ℕ)^4283*50000000000000^3259 ≤ 21049826783857^3259*2000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035470653 2000000000 21049826783857 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (667979179/5000000000 : ℝ)^4283 ≤ (7097593169807/100000000000000 : ℝ)^3259 := by
    have hnat : (667979179 : ℕ)^4283*100000000000000^3259 ≤ 7097593169807^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667979179 5000000000 7097593169807 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5973173421/10000000000 : ℝ)^4283 ≤ (50802753243161/100000000000000 : ℝ)^3259 := by
    have hnat : (5973173421 : ℕ)^4283*100000000000000^3259 ≤ 50802753243161^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5973173421 10000000000 50802753243161 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035470653/2000000000 : ℝ), (-667979179/5000000000 : ℝ), (5973173421/10000000000 : ℝ)] ![(21049826783857/50000000000000 : ℝ), (7097593169807/100000000000000 : ℝ), (50802753243161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035470653/2000000000 : ℝ)|^4283 ≤ (21049826783857/50000000000000 : ℝ)^3259
        have hw : |(1035470653/2000000000 : ℝ)|=(1035470653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-667979179/5000000000 : ℝ)|^4283 ≤ (7097593169807/100000000000000 : ℝ)^3259
        have hw : |(-667979179/5000000000 : ℝ)|=(667979179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5973173421/10000000000 : ℝ)|^4283 ≤ (50802753243161/100000000000000 : ℝ)^3259
        have hw : |(5973173421/10000000000 : ℝ)|=(5973173421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s0_6 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5177353289/10000000000 : ℝ)*x 0 + (5973173469/10000000000 : ℝ)*x 1 + (-267191649/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5177353289/10000000000 : ℝ)^4283 ≤ (4209965382419/10000000000000 : ℝ)^3259 := by
    have hnat : (5177353289 : ℕ)^4283*10000000000000^3259 ≤ 4209965382419^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177353289 10000000000 4209965382419 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5973173469/10000000000 : ℝ)^4283 ≤ (50802753779683/100000000000000 : ℝ)^3259 := by
    have hnat : (5973173469 : ℕ)^4283*100000000000000^3259 ≤ 50802753779683^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5973173469 10000000000 50802753779683 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267191649/2000000000 : ℝ)^4283 ≤ (7097592380837/100000000000000 : ℝ)^3259 := by
    have hnat : (267191649 : ℕ)^4283*100000000000000^3259 ≤ 7097592380837^3259*2000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267191649 2000000000 7097592380837 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5177353289/10000000000 : ℝ), (5973173469/10000000000 : ℝ), (-267191649/2000000000 : ℝ)] ![(4209965382419/10000000000000 : ℝ), (50802753779683/100000000000000 : ℝ), (7097592380837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5177353289/10000000000 : ℝ)|^4283 ≤ (4209965382419/10000000000000 : ℝ)^3259
        have hw : |(5177353289/10000000000 : ℝ)|=(5177353289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5973173469/10000000000 : ℝ)|^4283 ≤ (50802753779683/100000000000000 : ℝ)^3259
        have hw : |(5973173469/10000000000 : ℝ)|=(5973173469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-267191649/2000000000 : ℝ)|^4283 ≤ (7097592380837/100000000000000 : ℝ)^3259
        have hw : |(-267191649/2000000000 : ℝ)|=(267191649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s0_7 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4191081419/10000000000 : ℝ)*x 0 + (5536378693/10000000000 : ℝ)*x 1 + (3174089/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4191081419/10000000000 : ℝ)^4283 ≤ (15945141934417/50000000000000 : ℝ)^3259 := by
    have hnat : (4191081419 : ℕ)^4283*50000000000000^3259 ≤ 15945141934417^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4191081419 10000000000 15945141934417 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5536378693/10000000000 : ℝ)^4283 ≤ (179599704143/390625000000 : ℝ)^3259 := by
    have hnat : (5536378693 : ℕ)^4283*390625000000^3259 ≤ 179599704143^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5536378693 10000000000 179599704143 390625000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3174089/10000000 : ℝ)^4283 ≤ (22132191856287/100000000000000 : ℝ)^3259 := by
    have hnat : (3174089 : ℕ)^4283*100000000000000^3259 ≤ 22132191856287^3259*10000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3174089 10000000 22132191856287 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4191081419/10000000000 : ℝ), (5536378693/10000000000 : ℝ), (3174089/10000000 : ℝ)] ![(15945141934417/50000000000000 : ℝ), (179599704143/390625000000 : ℝ), (22132191856287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4191081419/10000000000 : ℝ)|^4283 ≤ (15945141934417/50000000000000 : ℝ)^3259
        have hw : |(4191081419/10000000000 : ℝ)|=(4191081419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5536378693/10000000000 : ℝ)|^4283 ≤ (179599704143/390625000000 : ℝ)^3259
        have hw : |(5536378693/10000000000 : ℝ)|=(5536378693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3174089/10000000 : ℝ)|^4283 ≤ (22132191856287/100000000000000 : ℝ)^3259
        have hw : |(3174089/10000000 : ℝ)|=(3174089/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1323_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1271/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (844/3125 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (2141/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2141 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2141*1^512 ≤ 0^512*1^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2141/512 : ℝ) ≤ (1083746973740272579/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2141 ≤ (1083746973740272579/50000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2141*50000000000000000000^512 ≤ 1083746973740272579^512*5^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1083746973740272579 50000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1083746973740272579/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2141 := by
      have hnat : (1 : ℕ)^512*1^2141 ≤ 1^2141*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (51083746973740272579/50000000000000000000 : ℝ) ≤ (5025705763251531/5000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (51083746973740272579/50000000000000000000 : ℝ)^512 ≤ (5025705763251531/5000000000000000 : ℝ)^2141 := by
      have hnat : (51083746973740272579 : ℕ)^512*5000000000000000^2141 ≤ 5025705763251531^2141*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51083746973740272579 50000000000000000000 5025705763251531 5000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5025705763251531/5000000000000000 : ℝ)) (X := (51083746973740272579/50000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (26083746973740272579/25000000000000000000 : ℝ) ≤ (2525705763251531/2500000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (26083746973740272579/25000000000000000000 : ℝ)^512 ≤ (2525705763251531/2500000000000000 : ℝ)^2141 := by
      have hnat : (26083746973740272579 : ℕ)^512*2500000000000000^2141 ≤ 2525705763251531^2141*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26083746973740272579 25000000000000000000 2525705763251531 2500000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2525705763251531/2500000000000000 : ℝ)) (X := (26083746973740272579/25000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(25705763251531/2000000000000000 : ℝ)*(0 : ℝ))^(2141/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(25705763251531/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1083746973740272579/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(25705763251531/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2141/512 : ℝ) := by
    rw [show (1 : ℝ)+(25705763251531/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5025705763251531/5000000000000000 : ℝ) by norm_num, show 1+(1083746973740272579/50000000000000000000 : ℝ)+(0 : ℝ)=(51083746973740272579/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1083746973740272579/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(25705763251531/2000000000000000 : ℝ)*(2/5 : ℝ))^(2141/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(25705763251531/2000000000000000 : ℝ)*(2/5 : ℝ)=(2525705763251531/2500000000000000 : ℝ) by norm_num, show 1+2*(1083746973740272579/50000000000000000000 : ℝ)=(26083746973740272579/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(25705763251531/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25705763251531/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(25705763251531/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25705763251531/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(25705763251531/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25705763251531/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1820431879/10000000000 : ℝ)*X 0 0+(6005163489/10000000000 : ℝ)*X 0 1+(4806355523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2751970871/5000000000 : ℝ)*X 1 0+(-1251387639/5000000000 : ℝ)*X 1 1+(300397231/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5503941027/10000000000 : ℝ)*X 2 0+(4806356029/10000000000 : ℝ)*X 2 1+(-500555157/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4181605107/10000000000 : ℝ)*X 0 0+(1553781561/5000000000 : ℝ)*X 0 1+(2800306737/5000000000 : ℝ)*X 0 2+(4181605107/10000000000 : ℝ)*X 1 0+(1553781561/5000000000 : ℝ)*X 1 1+(2800306737/5000000000 : ℝ)*X 1 2+(4181605107/10000000000 : ℝ)*X 2 0+(1553781561/5000000000 : ℝ)*X 2 1+(2800306737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1824989011/10000000000 : ℝ)*X 0 0+(2418621871/5000000000 : ℝ)*X 0 1+(5973173499/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1035470653/2000000000 : ℝ)*X 1 0+(-667979179/5000000000 : ℝ)*X 1 1+(5973173421/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5177353289/10000000000 : ℝ)*X 2 0+(5973173469/10000000000 : ℝ)*X 2 1+(-267191649/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4191081419/10000000000 : ℝ)*X 0 0+(5536378693/10000000000 : ℝ)*X 0 1+(3174089/10000000 : ℝ)*X 0 2+(4191081419/10000000000 : ℝ)*X 1 0+(5536378693/10000000000 : ℝ)*X 1 1+(3174089/10000000 : ℝ)*X 1 2+(4191081419/10000000000 : ℝ)*X 2 0+(5536378693/10000000000 : ℝ)*X 2 1+(3174089/10000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1243322450015598249/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (52204859/100000000000000 : ℝ)*(base1) + (7123099/50000000000000 : ℝ)*(base16) + (335282807/50000000000000 : ℝ)*(base19) + (23057917/4000000000000 : ℝ)*(base23) + (28926451/25000000000000 : ℝ)*(upper3) + (617641703774671/100000000000000 : ℝ)*(major0) + (617641703774671/100000000000000 : ℝ)*(major1) + (617641703774671/100000000000000 : ℝ)*(major2) + (417082275256059/50000000000000 : ℝ)*(sp0) + (208541414145091/25000000000000 : ℝ)*(sp1) + (834165764944251/100000000000000 : ℝ)*(sp2) + (401115837099539/100000000000000 : ℝ)*(sp3) + (1843084917/100000000000000 : ℝ)*(sp4) + (1093964601/100000000000000 : ℝ)*(sp7) + (401116983268999/100000000000000 : ℝ)*(f.failure) + (52135396337011/6250000000000 : ℝ)*(f.sum) + (6152648528699/100000000000000000000000000000 : ℝ)*base66 + (591371846371301/200000000000000000000000000000 : ℝ)*base67 + (516557163171301/200000000000000000000000000000 : ℝ)*base69 + (525171403771301/200000000000000000000000000000 : ℝ)*base71 + (233759486128699/100000000000000000000000000000 : ℝ)*base74 + (729674953771301/200000000000000000000000000000 : ℝ)*base75 + (715265065971301/200000000000000000000000000000 : ℝ)*base77 + (662523813771301/200000000000000000000000000000 : ℝ)*base79 + (101310425328699/100000000000000000000000000000 : ℝ)*base82 + (14541221/5000000000000000000000 : ℝ)*base90 + (14541221/5000000000000000000000 : ℝ)*base92 + (14541221/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1028677788412339558743/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73759321/20000000000000 : ℝ)*(base19) + (79729003/20000000000000 : ℝ)*(base23) + (11202957/50000000000000 : ℝ)*(base39) + (11328313/25000000000000 : ℝ)*(upper3) + (6368767/12500000000000 : ℝ)*(upper5) + (651827077019251/100000000000000 : ℝ)*(major0) + (651827077019251/100000000000000 : ℝ)*(major1) + (325913527306669/50000000000000 : ℝ)*(major2) + (165112549/20000000000000 : ℝ)*(sp1) + (221918517/25000000000000 : ℝ)*(sp2) + (176067195928929/20000000000000 : ℝ)*(sp4) + (176066957057059/20000000000000 : ℝ)*(sp5) + (35213388629259/4000000000000 : ℝ)*(sp6) + (423318097125121/100000000000000 : ℝ)*(sp7) + (423318097125121/100000000000000 : ℝ)*(f.failure) + (440168001025279/50000000000000 : ℝ)*(f.sum) + (537047962943759/200000000000000000000000000000 : ℝ)*base65 + (130119576460239/100000000000000000000000000000 : ℝ)*base67 + (100946871223281/200000000000000000000000000000 : ℝ)*base69 + (464086245639761/100000000000000000000000000000 : ℝ)*base72 + (1450117457143759/200000000000000000000000000000 : ℝ)*base73 + (75258500776719/200000000000000000000000000000 : ℝ)*base76 + (779343919776719/200000000000000000000000000000 : ℝ)*base78 + (653865322223281/200000000000000000000000000000 : ℝ)*base79 + (269686817723281/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (19558259/5000000000000000000000 : ℝ)*base90 + (19558259/5000000000000000000000 : ℝ)*base92 + (69558259/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1323_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1271/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (844/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1323_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1323_s1_0 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-401599037/2000000000 : ℝ)*x 0 + (5650752999/10000000000 : ℝ)*x 1 + (1260166547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (401599037/2000000000 : ℝ)^4283 ≤ (6062558633747/50000000000000 : ℝ)^3259 := by
    have hnat : (401599037 : ℕ)^4283*50000000000000^3259 ≤ 6062558633747^3259*2000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401599037 2000000000 6062558633747 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5650752999/10000000000 : ℝ)^4283 ≤ (2361491827651/5000000000000 : ℝ)^3259 := by
    have hnat : (5650752999 : ℕ)^4283*5000000000000^3259 ≤ 2361491827651^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5650752999 10000000000 2361491827651 5000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1260166547/2500000000 : ℝ)^4283 ≤ (4064504616711/10000000000000 : ℝ)^3259 := by
    have hnat : (1260166547 : ℕ)^4283*10000000000000^3259 ≤ 4064504616711^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260166547 2500000000 4064504616711 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-401599037/2000000000 : ℝ), (5650752999/10000000000 : ℝ), (1260166547/2500000000 : ℝ)] ![(6062558633747/50000000000000 : ℝ), (2361491827651/5000000000000 : ℝ), (4064504616711/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-401599037/2000000000 : ℝ)|^4283 ≤ (6062558633747/50000000000000 : ℝ)^3259
        have hw : |(-401599037/2000000000 : ℝ)|=(401599037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5650752999/10000000000 : ℝ)|^4283 ≤ (2361491827651/5000000000000 : ℝ)^3259
        have hw : |(5650752999/10000000000 : ℝ)|=(5650752999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1260166547/2500000000 : ℝ)|^4283 ≤ (4064504616711/10000000000000 : ℝ)^3259
        have hw : |(1260166547/2500000000 : ℝ)|=(1260166547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s1_1 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5407704819/10000000000 : ℝ)*x 0 + (-2334086681/10000000000 : ℝ)*x 1 + (5040666383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407704819/10000000000 : ℝ)^4283 ≤ (22289167129737/50000000000000 : ℝ)^3259 := by
    have hnat : (5407704819 : ℕ)^4283*50000000000000^3259 ≤ 22289167129737^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407704819 10000000000 22289167129737 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2334086681/10000000000 : ℝ)^4283 ≤ (2955323498519/20000000000000 : ℝ)^3259 := by
    have hnat : (2334086681 : ℕ)^4283*20000000000000^3259 ≤ 2955323498519^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2334086681 10000000000 2955323498519 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5040666383/10000000000 : ℝ)^4283 ≤ (5080631029191/12500000000000 : ℝ)^3259 := by
    have hnat : (5040666383 : ℕ)^4283*12500000000000^3259 ≤ 5080631029191^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5040666383 10000000000 5080631029191 12500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407704819/10000000000 : ℝ), (-2334086681/10000000000 : ℝ), (5040666383/10000000000 : ℝ)] ![(22289167129737/50000000000000 : ℝ), (2955323498519/20000000000000 : ℝ), (5080631029191/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407704819/10000000000 : ℝ)|^4283 ≤ (22289167129737/50000000000000 : ℝ)^3259
        have hw : |(5407704819/10000000000 : ℝ)|=(5407704819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2334086681/10000000000 : ℝ)|^4283 ≤ (2955323498519/20000000000000 : ℝ)^3259
        have hw : |(-2334086681/10000000000 : ℝ)|=(2334086681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5040666383/10000000000 : ℝ)|^4283 ≤ (5080631029191/12500000000000 : ℝ)^3259
        have hw : |(5040666383/10000000000 : ℝ)|=(5040666383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s1_2 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5407704971/10000000000 : ℝ)*x 0 + (126016649/250000000 : ℝ)*x 1 + (-1167043511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407704971/10000000000 : ℝ)^4283 ≤ (11144583976547/25000000000000 : ℝ)^3259 := by
    have hnat : (5407704971 : ℕ)^4283*25000000000000^3259 ≤ 11144583976547^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407704971 10000000000 11144583976547 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126016649/250000000 : ℝ)^4283 ≤ (2540315234437/6250000000000 : ℝ)^3259 := by
    have hnat : (126016649 : ℕ)^4283*6250000000000^3259 ≤ 2540315234437^3259*250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126016649 250000000 2540315234437 6250000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1167043511/5000000000 : ℝ)^4283 ≤ (2955324065941/20000000000000 : ℝ)^3259 := by
    have hnat : (1167043511 : ℕ)^4283*20000000000000^3259 ≤ 2955324065941^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167043511 5000000000 2955324065941 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407704971/10000000000 : ℝ), (126016649/250000000 : ℝ), (-1167043511/5000000000 : ℝ)] ![(11144583976547/25000000000000 : ℝ), (2540315234437/6250000000000 : ℝ), (2955324065941/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407704971/10000000000 : ℝ)|^4283 ≤ (11144583976547/25000000000000 : ℝ)^3259
        have hw : |(5407704971/10000000000 : ℝ)|=(5407704971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(126016649/250000000 : ℝ)|^4283 ≤ (2540315234437/6250000000000 : ℝ)^3259
        have hw : |(126016649/250000000 : ℝ)|=(126016649/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1167043511/5000000000 : ℝ)|^4283 ≤ (2955324065941/20000000000000 : ℝ)^3259
        have hw : |(-1167043511/5000000000 : ℝ)|=(1167043511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s1_3 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4295685013/10000000000 : ℝ)*x 0 + (3705085791/10000000000 : ℝ)*x 1 + (2486913649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4295685013/10000000000 : ℝ)^4283 ≤ (32940388575617/100000000000000 : ℝ)^3259 := by
    have hnat : (4295685013 : ℕ)^4283*100000000000000^3259 ≤ 32940388575617^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295685013 10000000000 32940388575617 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3705085791/10000000000 : ℝ)^4283 ≤ (27121377717831/100000000000000 : ℝ)^3259 := by
    have hnat : (3705085791 : ℕ)^4283*100000000000000^3259 ≤ 27121377717831^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705085791 10000000000 27121377717831 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2486913649/5000000000 : ℝ)^4283 ≤ (19969116846687/50000000000000 : ℝ)^3259 := by
    have hnat : (2486913649 : ℕ)^4283*50000000000000^3259 ≤ 19969116846687^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2486913649 5000000000 19969116846687 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4295685013/10000000000 : ℝ), (3705085791/10000000000 : ℝ), (2486913649/5000000000 : ℝ)] ![(32940388575617/100000000000000 : ℝ), (27121377717831/100000000000000 : ℝ), (19969116846687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4295685013/10000000000 : ℝ)|^4283 ≤ (32940388575617/100000000000000 : ℝ)^3259
        have hw : |(4295685013/10000000000 : ℝ)|=(4295685013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3705085791/10000000000 : ℝ)|^4283 ≤ (27121377717831/100000000000000 : ℝ)^3259
        have hw : |(3705085791/10000000000 : ℝ)|=(3705085791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2486913649/5000000000 : ℝ)|^4283 ≤ (19969116846687/50000000000000 : ℝ)^3259
        have hw : |(2486913649/5000000000 : ℝ)|=(2486913649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s1_4 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2008567873/10000000000 : ℝ)*x 0 + (2524216623/5000000000 : ℝ)*x 1 + (705355313/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2008567873/10000000000 : ℝ)^4283 ≤ (6064831084809/50000000000000 : ℝ)^3259 := by
    have hnat : (2008567873 : ℕ)^4283*50000000000000^3259 ≤ 6064831084809^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008567873 10000000000 6064831084809 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2524216623/5000000000 : ℝ)^4283 ≤ (20363686843141/50000000000000 : ℝ)^3259 := by
    have hnat : (2524216623 : ℕ)^4283*50000000000000^3259 ≤ 20363686843141^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2524216623 5000000000 20363686843141 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (705355313/1250000000 : ℝ)^4283 ≤ (47142964129461/100000000000000 : ℝ)^3259 := by
    have hnat : (705355313 : ℕ)^4283*100000000000000^3259 ≤ 47142964129461^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      705355313 1250000000 47142964129461 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2008567873/10000000000 : ℝ), (2524216623/5000000000 : ℝ), (705355313/1250000000 : ℝ)] ![(6064831084809/50000000000000 : ℝ), (20363686843141/50000000000000 : ℝ), (47142964129461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2008567873/10000000000 : ℝ)|^4283 ≤ (6064831084809/50000000000000 : ℝ)^3259
        have hw : |(-2008567873/10000000000 : ℝ)|=(2008567873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2524216623/5000000000 : ℝ)|^4283 ≤ (20363686843141/50000000000000 : ℝ)^3259
        have hw : |(2524216623/5000000000 : ℝ)|=(2524216623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(705355313/1250000000 : ℝ)|^4283 ≤ (47142964129461/100000000000000 : ℝ)^3259
        have hw : |(705355313/1250000000 : ℝ)|=(705355313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s1_5 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312412707/2500000000 : ℝ)*x 0 + (-346382153/2000000000 : ℝ)*x 1 + (5642842089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312412707/2500000000 : ℝ)^4283 ≤ (10718487295633/25000000000000 : ℝ)^3259 := by
    have hnat : (1312412707 : ℕ)^4283*25000000000000^3259 ≤ 10718487295633^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312412707 2500000000 10718487295633 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346382153/2000000000 : ℝ)^4283 ≤ (9983091239717/100000000000000 : ℝ)^3259 := by
    have hnat : (346382153 : ℕ)^4283*100000000000000^3259 ≤ 9983091239717^3259*2000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346382153 2000000000 9983091239717 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5642842089/10000000000 : ℝ)^4283 ≤ (47142959572967/100000000000000 : ℝ)^3259 := by
    have hnat : (5642842089 : ℕ)^4283*100000000000000^3259 ≤ 47142959572967^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5642842089 10000000000 47142959572967 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312412707/2500000000 : ℝ), (-346382153/2000000000 : ℝ), (5642842089/10000000000 : ℝ)] ![(10718487295633/25000000000000 : ℝ), (9983091239717/100000000000000 : ℝ), (47142959572967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312412707/2500000000 : ℝ)|^4283 ≤ (10718487295633/25000000000000 : ℝ)^3259
        have hw : |(1312412707/2500000000 : ℝ)|=(1312412707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-346382153/2000000000 : ℝ)|^4283 ≤ (9983091239717/100000000000000 : ℝ)^3259
        have hw : |(-346382153/2000000000 : ℝ)|=(346382153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5642842089/10000000000 : ℝ)|^4283 ≤ (47142959572967/100000000000000 : ℝ)^3259
        have hw : |(5642842089/10000000000 : ℝ)|=(5642842089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s1_6 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2624825299/5000000000 : ℝ)*x 0 + (1410710481/2500000000 : ℝ)*x 1 + (-1731911329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2624825299/5000000000 : ℝ)^4283 ≤ (4287394671391/10000000000000 : ℝ)^3259 := by
    have hnat : (2624825299 : ℕ)^4283*10000000000000^3259 ≤ 4287394671391^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624825299 5000000000 4287394671391 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1410710481/2500000000 : ℝ)^4283 ≤ (942859155227/2000000000000 : ℝ)^3259 := by
    have hnat : (1410710481 : ℕ)^4283*2000000000000^3259 ≤ 942859155227^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1410710481 2500000000 942859155227 2000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1731911329/10000000000 : ℝ)^4283 ≤ (499154775611/5000000000000 : ℝ)^3259 := by
    have hnat : (1731911329 : ℕ)^4283*5000000000000^3259 ≤ 499154775611^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1731911329 10000000000 499154775611 5000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2624825299/5000000000 : ℝ), (1410710481/2500000000 : ℝ), (-1731911329/10000000000 : ℝ)] ![(4287394671391/10000000000000 : ℝ), (942859155227/2000000000000 : ℝ), (499154775611/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2624825299/5000000000 : ℝ)|^4283 ≤ (4287394671391/10000000000000 : ℝ)^3259
        have hw : |(2624825299/5000000000 : ℝ)|=(2624825299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1410710481/2500000000 : ℝ)|^4283 ≤ (942859155227/2000000000000 : ℝ)^3259
        have hw : |(1410710481/2500000000 : ℝ)|=(1410710481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1731911329/10000000000 : ℝ)|^4283 ≤ (499154775611/5000000000000 : ℝ)^3259
        have hw : |(-1731911329/10000000000 : ℝ)|=(1731911329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s1_7 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4296875303/10000000000 : ℝ)*x 0 + (99153487/200000000 : ℝ)*x 1 + (3721537201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296875303/10000000000 : ℝ)^4283 ≤ (32952384444003/100000000000000 : ℝ)^3259 := by
    have hnat : (4296875303 : ℕ)^4283*100000000000000^3259 ≤ 32952384444003^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296875303 10000000000 32952384444003 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99153487/200000000 : ℝ)^4283 ≤ (7953572837827/20000000000000 : ℝ)^3259 := by
    have hnat : (99153487 : ℕ)^4283*20000000000000^3259 ≤ 7953572837827^3259*200000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99153487 200000000 7953572837827 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3721537201/10000000000 : ℝ)^4283 ≤ (27279751343371/100000000000000 : ℝ)^3259 := by
    have hnat : (3721537201 : ℕ)^4283*100000000000000^3259 ≤ 27279751343371^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3721537201 10000000000 27279751343371 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296875303/10000000000 : ℝ), (99153487/200000000 : ℝ), (3721537201/10000000000 : ℝ)] ![(32952384444003/100000000000000 : ℝ), (7953572837827/20000000000000 : ℝ), (27279751343371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296875303/10000000000 : ℝ)|^4283 ≤ (32952384444003/100000000000000 : ℝ)^3259
        have hw : |(4296875303/10000000000 : ℝ)|=(4296875303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(99153487/200000000 : ℝ)|^4283 ≤ (7953572837827/20000000000000 : ℝ)^3259
        have hw : |(99153487/200000000 : ℝ)|=(99153487/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3721537201/10000000000 : ℝ)|^4283 ≤ (27279751343371/100000000000000 : ℝ)^3259
        have hw : |(3721537201/10000000000 : ℝ)|=(3721537201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1323_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (844/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6711/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9803/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (844/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1271/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (844/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1271/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (844/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1271/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (844/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1271/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (844/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1271/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (844/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1271/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1271/100000 : ℝ) ^ (2141/512 : ℝ) ≤ (5904566517/500000000000000000 : ℝ) := by
    have hpowers : (1271/100000 : ℝ)^2141 ≤ (5904566517/500000000000000000 : ℝ)^512 := by
      have hnat : (1271 : ℕ)^2141*500000000000000000^512 ≤ 5904566517^512*100000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1271 100000 5904566517 500000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1271/100000 : ℝ)) (X := (5904566517/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hpowhi : (844/3125 : ℝ) ^ (2141/512 : ℝ) ≤ (26217160081919213/6250000000000000000 : ℝ) := by
    have hpowers : (844/3125 : ℝ)^2141 ≤ (26217160081919213/6250000000000000000 : ℝ)^512 := by
      have hnat : (844 : ℕ)^2141*6250000000000000000^512 ≤ 26217160081919213^512*3125^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        844 3125 26217160081919213 6250000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (844/3125 : ℝ)) (X := (26217160081919213/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (250000005904566517/250000000000000000 : ℝ) ≤ (500000002824043/500000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (250000005904566517/250000000000000000 : ℝ)^512 ≤ (500000002824043/500000000000000 : ℝ)^2141 := by
      have hnat : (250000005904566517 : ℕ)^512*500000000000000^2141 ≤ 500000002824043^2141*250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250000005904566517 250000000000000000 500000002824043 500000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000002824043/500000000000000 : ℝ)) (X := (250000005904566517/250000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12552434467778001351/12500000000000000000 : ℝ) ≤ (10010015398726429/10000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (12552434467778001351/12500000000000000000 : ℝ)^512 ≤ (10010015398726429/10000000000000000 : ℝ)^2141 := by
      have hnat : (12552434467778001351 : ℕ)^512*10000000000000000^2141 ≤ 10010015398726429^2141*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12552434467778001351 12500000000000000000 10010015398726429 10000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010015398726429/10000000000000000 : ℝ)) (X := (12552434467778001351/12500000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3151217160081919213/3125000000000000000 : ℝ) ≤ (5010015370485999/5000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (3151217160081919213/3125000000000000000 : ℝ)^512 ≤ (5010015370485999/5000000000000000 : ℝ)^2141 := by
      have hnat : (3151217160081919213 : ℕ)^512*5000000000000000^2141 ≤ 5010015370485999^2141*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3151217160081919213 3125000000000000000 5010015370485999 5000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010015370485999/5000000000000000 : ℝ)) (X := (3151217160081919213/3125000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5904566517/500000000000000000 : ℝ) ≤ ((128672271226829828711/128685000000000000000 : ℝ)+2*(10015342245569/2573700000000000 : ℝ)*(1271/100000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (128672271226829828711/128685000000000000000 : ℝ)+2*(10015342245569/2573700000000000 : ℝ)*(1271/100000 : ℝ)=(500000002824043/500000000000000 : ℝ) by norm_num, show 1+2*(5904566517/500000000000000000 : ℝ)=(250000005904566517/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26217160081919213/6250000000000000000 : ℝ)+(5904566517/500000000000000000 : ℝ) ≤ ((128672271226829828711/128685000000000000000 : ℝ)+(10015342245569/2573700000000000 : ℝ)*((844/3125 : ℝ)+(1271/100000 : ℝ)))^(2141/512 : ℝ) := by
    rw [show (128672271226829828711/128685000000000000000 : ℝ)+(10015342245569/2573700000000000 : ℝ)*((844/3125 : ℝ)+(1271/100000 : ℝ))=(10010015398726429/10000000000000000 : ℝ) by norm_num, show 1+(26217160081919213/6250000000000000000 : ℝ)+(5904566517/500000000000000000 : ℝ)=(12552434467778001351/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26217160081919213/6250000000000000000 : ℝ) ≤ ((128672271226829828711/128685000000000000000 : ℝ)+2*(10015342245569/2573700000000000 : ℝ)*(844/3125 : ℝ))^(2141/512 : ℝ) := by
    rw [show (128672271226829828711/128685000000000000000 : ℝ)+2*(10015342245569/2573700000000000 : ℝ)*(844/3125 : ℝ)=(5010015370485999/5000000000000000 : ℝ) by norm_num, show 1+2*(26217160081919213/6250000000000000000 : ℝ)=(3151217160081919213/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (128672271226829828711/128685000000000000000 : ℝ)*(X 1 0+X 2 0)+(10015342245569/2573700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (1271/100000 : ℝ)) (hi := (844/3125 : ℝ)) (c := (128672271226829828711/128685000000000000000 : ℝ)) (alpha := (10015342245569/2573700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (128672271226829828711/128685000000000000000 : ℝ)*(X 0 1+X 2 1)+(10015342245569/2573700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (1271/100000 : ℝ)) (hi := (844/3125 : ℝ)) (c := (128672271226829828711/128685000000000000000 : ℝ)) (alpha := (10015342245569/2573700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (128672271226829828711/128685000000000000000 : ℝ)*(X 0 2+X 1 2)+(10015342245569/2573700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (1271/100000 : ℝ)) (hi := (844/3125 : ℝ)) (c := (128672271226829828711/128685000000000000000 : ℝ)) (alpha := (10015342245569/2573700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-401599037/2000000000 : ℝ)*X 0 0+(5650752999/10000000000 : ℝ)*X 0 1+(1260166547/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5407704819/10000000000 : ℝ)*X 1 0+(-2334086681/10000000000 : ℝ)*X 1 1+(5040666383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5407704971/10000000000 : ℝ)*X 2 0+(126016649/250000000 : ℝ)*X 2 1+(-1167043511/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4295685013/10000000000 : ℝ)*X 0 0+(3705085791/10000000000 : ℝ)*X 0 1+(2486913649/5000000000 : ℝ)*X 0 2+(4295685013/10000000000 : ℝ)*X 1 0+(3705085791/10000000000 : ℝ)*X 1 1+(2486913649/5000000000 : ℝ)*X 1 2+(4295685013/10000000000 : ℝ)*X 2 0+(3705085791/10000000000 : ℝ)*X 2 1+(2486913649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2008567873/10000000000 : ℝ)*X 0 0+(2524216623/5000000000 : ℝ)*X 0 1+(705355313/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1312412707/2500000000 : ℝ)*X 1 0+(-346382153/2000000000 : ℝ)*X 1 1+(5642842089/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2624825299/5000000000 : ℝ)*X 2 0+(1410710481/2500000000 : ℝ)*X 2 1+(-1731911329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4296875303/10000000000 : ℝ)*X 0 0+(99153487/200000000 : ℝ)*X 0 1+(3721537201/10000000000 : ℝ)*X 0 2+(4296875303/10000000000 : ℝ)*X 1 0+(99153487/200000000 : ℝ)*X 1 1+(3721537201/10000000000 : ℝ)*X 1 2+(4296875303/10000000000 : ℝ)*X 2 0+(99153487/200000000 : ℝ)*X 2 1+(3721537201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15052598719569993795498400617/2144750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15573223/20000000000000 : ℝ)*(base1) + (567683977/50000000000000 : ℝ)*(base19) + (295360119/25000000000000 : ℝ)*(base23) + (104573967/50000000000000 : ℝ)*(upper3) + (41809333/50000000000000 : ℝ)*(upper5) + (1213656165360251/100000000000000 : ℝ)*(major0) + (1213656165360251/100000000000000 : ℝ)*(major1) + (1213656165360251/100000000000000 : ℝ)*(major2) + (1639117899312133/100000000000000 : ℝ)*(sp0) + (204890305300081/12500000000000 : ℝ)*(sp1) + (20980766673/1280000000 : ℝ)*(sp2) + (197046292431007/25000000000000 : ℝ)*(sp3) + (5756322583/100000000000000 : ℝ)*(sp4) + (3271416869/100000000000000 : ℝ)*(sp7) + (197047129751753/25000000000000 : ℝ)*(f.failure) + (1639123577768601/100000000000000 : ℝ)*(f.sum) + (102728436238381/32171250000000000000000000000 : ℝ)*base65 + (6202279565997805487/4289500000000000000000000000000000 : ℝ)*base67 + (21253451894490805487/4289500000000000000000000000000000 : ℝ)*base69 + (25601655700897805487/4289500000000000000000000000000000 : ℝ)*base71 + (20341399195969/128685000000000000000000000000 : ℝ)*base73 + (525346736244805487/4289500000000000000000000000000000 : ℝ)*base75 + (27354831559959305487/4289500000000000000000000000000000 : ℝ)*base77 + (47495178275505305487/4289500000000000000000000000000000 : ℝ)*base79 + (20822294651479/8042812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1107413/1250000000000000000000 : ℝ)*base89 + (1107413/1250000000000000000000 : ℝ)*base91 + (1107413/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10017215993652818352753596191/1072375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7829839/50000000000000 : ℝ)*(base1) + (211349087/12500000000000 : ℝ)*(base19) + (1548423251/100000000000000 : ℝ)*(base23) + (78586639/50000000000000 : ℝ)*(upper3) + (61668599/25000000000000 : ℝ)*(upper5) + (1245657366445319/100000000000000 : ℝ)*(major0) + (1245657366445319/100000000000000 : ℝ)*(major1) + (1245657366445319/100000000000000 : ℝ)*(major2) + (8122857/97656250000 : ℝ)*(sp1) + (1509308263/25000000000000 : ℝ)*(sp2) + (841171639035871/50000000000000 : ℝ)*(sp4) + (1682333253813799/100000000000000 : ℝ)*(sp5) + (1682335676755761/100000000000000 : ℝ)*(sp6) + (50560696465451/6250000000000 : ℝ)*(sp7) + (404485579553447/50000000000000 : ℝ)*(f.failure) + (52573226950377/3125000000000 : ℝ)*(f.sum) + (124493737506659/128685000000000000000000000000 : ℝ)*base66 + (14415079994050434603/4289500000000000000000000000000000 : ℝ)*base67 + (11325094693096434603/4289500000000000000000000000000000 : ℝ)*base69 + (9414938185890434603/4289500000000000000000000000000000 : ℝ)*base71 + (48597371445517/64342500000000000000000000000 : ℝ)*base74 + (33651578928209934603/4289500000000000000000000000000000 : ℝ)*base75 + (8440915447446565397/4289500000000000000000000000000000 : ℝ)*base78 + (702837265746434603/4289500000000000000000000000000000 : ℝ)*base79 + (114446542562239/32171250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (9158213/2500000000000000000000 : ℝ)*base90 + (9158213/2500000000000000000000 : ℝ)*base92 + (9158213/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1323_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (844/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6711/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9803/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1323_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1323_s2_0 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049827023/10000000000 : ℝ)*x 0 + (685632871/1250000000 : ℝ)*x 1 + (1294897379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049827023/10000000000 : ℝ)^4283 ≤ (12458164880217/100000000000000 : ℝ)^3259 := by
    have hnat : (2049827023 : ℕ)^4283*100000000000000^3259 ≤ 12458164880217^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049827023 10000000000 12458164880217 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685632871/1250000000 : ℝ)^4283 ≤ (2270914114033/5000000000000 : ℝ)^3259 := by
    have hnat : (685632871 : ℕ)^4283*5000000000000^3259 ≤ 2270914114033^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685632871 1250000000 2270914114033 5000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294897379/2500000000 : ℝ)^4283 ≤ (842471056551/2000000000000 : ℝ)^3259 := by
    have hnat : (1294897379 : ℕ)^4283*2000000000000^3259 ≤ 842471056551^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294897379 2500000000 842471056551 2000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049827023/10000000000 : ℝ), (685632871/1250000000 : ℝ), (1294897379/2500000000 : ℝ)] ![(12458164880217/100000000000000 : ℝ), (2270914114033/5000000000000 : ℝ), (842471056551/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049827023/10000000000 : ℝ)|^4283 ≤ (12458164880217/100000000000000 : ℝ)^3259
        have hw : |(-2049827023/10000000000 : ℝ)|=(2049827023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685632871/1250000000 : ℝ)|^4283 ≤ (2270914114033/5000000000000 : ℝ)^3259
        have hw : |(685632871/1250000000 : ℝ)|=(685632871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294897379/2500000000 : ℝ)|^4283 ≤ (842471056551/2000000000000 : ℝ)^3259
        have hw : |(1294897379/2500000000 : ℝ)|=(1294897379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s2_1 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367306763/10000000000 : ℝ)*x 0 + (-2207836867/10000000000 : ℝ)*x 1 + (1294897259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367306763/10000000000 : ℝ)^4283 ≤ (2207059531043/5000000000000 : ℝ)^3259 := by
    have hnat : (5367306763 : ℕ)^4283*5000000000000^3259 ≤ 2207059531043^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367306763 10000000000 2207059531043 5000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207836867/10000000000 : ℝ)^4283 ≤ (1373526167193/10000000000000 : ℝ)^3259 := by
    have hnat : (2207836867 : ℕ)^4283*10000000000000^3259 ≤ 1373526167193^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207836867 10000000000 1373526167193 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294897259/2500000000 : ℝ)^4283 ≤ (42123547697347/100000000000000 : ℝ)^3259 := by
    have hnat : (1294897259 : ℕ)^4283*100000000000000^3259 ≤ 42123547697347^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294897259 2500000000 42123547697347 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367306763/10000000000 : ℝ), (-2207836867/10000000000 : ℝ), (1294897259/2500000000 : ℝ)] ![(2207059531043/5000000000000 : ℝ), (1373526167193/10000000000000 : ℝ), (42123547697347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367306763/10000000000 : ℝ)|^4283 ≤ (2207059531043/5000000000000 : ℝ)^3259
        have hw : |(5367306763/10000000000 : ℝ)|=(5367306763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2207836867/10000000000 : ℝ)|^4283 ≤ (1373526167193/10000000000000 : ℝ)^3259
        have hw : |(-2207836867/10000000000 : ℝ)|=(2207836867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294897259/2500000000 : ℝ)|^4283 ≤ (42123547697347/100000000000000 : ℝ)^3259
        have hw : |(1294897259/2500000000 : ℝ)|=(1294897259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s2_2 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536730609/1000000000 : ℝ)*x 0 + (51795897/100000000 : ℝ)*x 1 + (-2207836887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536730609/1000000000 : ℝ)^4283 ≤ (1379411979593/3125000000000 : ℝ)^3259 := by
    have hnat : (536730609 : ℕ)^4283*3125000000000^3259 ≤ 1379411979593^3259*1000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536730609 1000000000 1379411979593 3125000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51795897/100000000 : ℝ)^4283 ≤ (2632722174633/6250000000000 : ℝ)^3259 := by
    have hnat : (51795897 : ℕ)^4283*6250000000000^3259 ≤ 2632722174633^3259*100000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51795897 100000000 2632722174633 6250000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2207836887/10000000000 : ℝ)^4283 ≤ (1716907729431/12500000000000 : ℝ)^3259 := by
    have hnat : (2207836887 : ℕ)^4283*12500000000000^3259 ≤ 1716907729431^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207836887 10000000000 1716907729431 12500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536730609/1000000000 : ℝ), (51795897/100000000 : ℝ), (-2207836887/10000000000 : ℝ)] ![(1379411979593/3125000000000 : ℝ), (2632722174633/6250000000000 : ℝ), (1716907729431/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536730609/1000000000 : ℝ)|^4283 ≤ (1379411979593/3125000000000 : ℝ)^3259
        have hw : |(536730609/1000000000 : ℝ)|=(536730609/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51795897/100000000 : ℝ)|^4283 ≤ (2632722174633/6250000000000 : ℝ)^3259
        have hw : |(51795897/100000000 : ℝ)|=(51795897/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2207836887/10000000000 : ℝ)|^4283 ≤ (1716907729431/12500000000000 : ℝ)^3259
        have hw : |(-2207836887/10000000000 : ℝ)|=(2207836887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s2_3 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (864974859/2000000000 : ℝ)*x 0 + (4018198113/10000000000 : ℝ)*x 1 + (4653472099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864974859/2000000000 : ℝ)^4283 ≤ (6646972394967/20000000000000 : ℝ)^3259 := by
    have hnat : (864974859 : ℕ)^4283*20000000000000^3259 ≤ 6646972394967^3259*2000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864974859 2000000000 6646972394967 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4018198113/10000000000 : ℝ)^4283 ≤ (3017277795727/10000000000000 : ℝ)^3259 := by
    have hnat : (4018198113 : ℕ)^4283*10000000000000^3259 ≤ 3017277795727^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018198113 10000000000 3017277795727 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4653472099/10000000000 : ℝ)^4283 ≤ (1143511251767/3125000000000 : ℝ)^3259 := by
    have hnat : (4653472099 : ℕ)^4283*3125000000000^3259 ≤ 1143511251767^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4653472099 10000000000 1143511251767 3125000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864974859/2000000000 : ℝ), (4018198113/10000000000 : ℝ), (4653472099/10000000000 : ℝ)] ![(6646972394967/20000000000000 : ℝ), (3017277795727/10000000000000 : ℝ), (1143511251767/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864974859/2000000000 : ℝ)|^4283 ≤ (6646972394967/20000000000000 : ℝ)^3259
        have hw : |(864974859/2000000000 : ℝ)|=(864974859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4018198113/10000000000 : ℝ)|^4283 ≤ (3017277795727/10000000000000 : ℝ)^3259
        have hw : |(4018198113/10000000000 : ℝ)|=(4018198113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4653472099/10000000000 : ℝ)|^4283 ≤ (1143511251767/3125000000000 : ℝ)^3259
        have hw : |(4653472099/10000000000 : ℝ)|=(4653472099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s2_4 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049898519/10000000000 : ℝ)*x 0 + (647693241/1250000000 : ℝ)*x 1 + (2741544381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049898519/10000000000 : ℝ)^4283 ≤ (6229367972053/50000000000000 : ℝ)^3259 := by
    have hnat : (2049898519 : ℕ)^4283*50000000000000^3259 ≤ 6229367972053^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049898519 10000000000 6229367972053 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647693241/1250000000 : ℝ)^4283 ≤ (8428892810277/20000000000000 : ℝ)^3259 := by
    have hnat : (647693241 : ℕ)^4283*20000000000000^3259 ≤ 8428892810277^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647693241 1250000000 8428892810277 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2741544381/5000000000 : ℝ)^4283 ≤ (9079359996807/20000000000000 : ℝ)^3259 := by
    have hnat : (2741544381 : ℕ)^4283*20000000000000^3259 ≤ 9079359996807^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741544381 5000000000 9079359996807 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049898519/10000000000 : ℝ), (647693241/1250000000 : ℝ), (2741544381/5000000000 : ℝ)] ![(6229367972053/50000000000000 : ℝ), (8428892810277/20000000000000 : ℝ), (9079359996807/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049898519/10000000000 : ℝ)|^4283 ≤ (6229367972053/50000000000000 : ℝ)^3259
        have hw : |(-2049898519/10000000000 : ℝ)|=(2049898519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647693241/1250000000 : ℝ)|^4283 ≤ (8428892810277/20000000000000 : ℝ)^3259
        have hw : |(647693241/1250000000 : ℝ)|=(647693241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2741544381/5000000000 : ℝ)|^4283 ≤ (9079359996807/20000000000000 : ℝ)^3259
        have hw : |(2741544381/5000000000 : ℝ)|=(2741544381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s2_5 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288735169/10000000000 : ℝ)*x 0 + (-1904336629/10000000000 : ℝ)*x 1 + (5483088817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288735169/10000000000 : ℝ)^4283 ≤ (8658787342507/20000000000000 : ℝ)^3259 := by
    have hnat : (5288735169 : ℕ)^4283*20000000000000^3259 ≤ 8658787342507^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288735169 10000000000 8658787342507 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1904336629/10000000000 : ℝ)^4283 ≤ (11309262685261/100000000000000 : ℝ)^3259 := by
    have hnat : (1904336629 : ℕ)^4283*100000000000000^3259 ≤ 11309262685261^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904336629 10000000000 11309262685261 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5483088817/10000000000 : ℝ)^4283 ≤ (45396800582483/100000000000000 : ℝ)^3259 := by
    have hnat : (5483088817 : ℕ)^4283*100000000000000^3259 ≤ 45396800582483^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483088817 10000000000 45396800582483 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288735169/10000000000 : ℝ), (-1904336629/10000000000 : ℝ), (5483088817/10000000000 : ℝ)] ![(8658787342507/20000000000000 : ℝ), (11309262685261/100000000000000 : ℝ), (45396800582483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288735169/10000000000 : ℝ)|^4283 ≤ (8658787342507/20000000000000 : ℝ)^3259
        have hw : |(5288735169/10000000000 : ℝ)|=(5288735169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1904336629/10000000000 : ℝ)|^4283 ≤ (11309262685261/100000000000000 : ℝ)^3259
        have hw : |(-1904336629/10000000000 : ℝ)|=(1904336629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5483088817/10000000000 : ℝ)|^4283 ≤ (45396800582483/100000000000000 : ℝ)^3259
        have hw : |(5483088817/10000000000 : ℝ)|=(5483088817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s2_6 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330545953/625000000 : ℝ)*x 0 + (5483088769/10000000000 : ℝ)*x 1 + (-1904336587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330545953/625000000 : ℝ)^4283 ≤ (676467774413/1562500000000 : ℝ)^3259 := by
    have hnat : (330545953 : ℕ)^4283*1562500000000^3259 ≤ 676467774413^3259*625000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330545953 625000000 676467774413 1562500000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5483088769/10000000000 : ℝ)^4283 ≤ (45396800060201/100000000000000 : ℝ)^3259 := by
    have hnat : (5483088769 : ℕ)^4283*100000000000000^3259 ≤ 45396800060201^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483088769 10000000000 45396800060201 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1904336587/10000000000 : ℝ)^4283 ≤ (2261852471493/20000000000000 : ℝ)^3259 := by
    have hnat : (1904336587 : ℕ)^4283*20000000000000^3259 ≤ 2261852471493^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904336587 10000000000 2261852471493 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330545953/625000000 : ℝ), (5483088769/10000000000 : ℝ), (-1904336587/10000000000 : ℝ)] ![(676467774413/1562500000000 : ℝ), (45396800060201/100000000000000 : ℝ), (2261852471493/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330545953/625000000 : ℝ)|^4283 ≤ (676467774413/1562500000000 : ℝ)^3259
        have hw : |(330545953/625000000 : ℝ)|=(330545953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5483088769/10000000000 : ℝ)|^4283 ≤ (45396800060201/100000000000000 : ℝ)^3259
        have hw : |(5483088769/10000000000 : ℝ)|=(5483088769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1904336587/10000000000 : ℝ)|^4283 ≤ (2261852471493/20000000000000 : ℝ)^3259
        have hw : |(-1904336587/10000000000 : ℝ)|=(1904336587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s2_7 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081255333/2500000000 : ℝ)*x 0 + (1162350311/2500000000 : ℝ)*x 1 + (4022309387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081255333/2500000000 : ℝ)^4283 ≤ (33236346929029/100000000000000 : ℝ)^3259 := by
    have hnat : (1081255333 : ℕ)^4283*100000000000000^3259 ≤ 33236346929029^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081255333 2500000000 33236346929029 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1162350311/2500000000 : ℝ)^4283 ≤ (1827514839719/5000000000000 : ℝ)^3259 := by
    have hnat : (1162350311 : ℕ)^4283*5000000000000^3259 ≤ 1827514839719^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162350311 2500000000 1827514839719 5000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4022309387/10000000000 : ℝ)^4283 ≤ (3021335625971/10000000000000 : ℝ)^3259 := by
    have hnat : (4022309387 : ℕ)^4283*10000000000000^3259 ≤ 3021335625971^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022309387 10000000000 3021335625971 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081255333/2500000000 : ℝ), (1162350311/2500000000 : ℝ), (4022309387/10000000000 : ℝ)] ![(33236346929029/100000000000000 : ℝ), (1827514839719/5000000000000 : ℝ), (3021335625971/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081255333/2500000000 : ℝ)|^4283 ≤ (33236346929029/100000000000000 : ℝ)^3259
        have hw : |(1081255333/2500000000 : ℝ)|=(1081255333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1162350311/2500000000 : ℝ)|^4283 ≤ (1827514839719/5000000000000 : ℝ)^3259
        have hw : |(1162350311/2500000000 : ℝ)|=(1162350311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4022309387/10000000000 : ℝ)|^4283 ≤ (3021335625971/10000000000000 : ℝ)^3259
        have hw : |(4022309387/10000000000 : ℝ)|=(4022309387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1323_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9803/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6711/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (389/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16181/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9803/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6711/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9803/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6711/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9803/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6711/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9803/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6711/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9803/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6711/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9803/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6711/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6711/100000 : ℝ) ^ (2141/512 : ℝ) ≤ (620891708734513/50000000000000000000 : ℝ) := by
    have hpowers : (6711/100000 : ℝ)^2141 ≤ (620891708734513/50000000000000000000 : ℝ)^512 := by
      have hnat : (6711 : ℕ)^2141*50000000000000000000^512 ≤ 620891708734513^512*100000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6711 100000 620891708734513 50000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6711/100000 : ℝ)) (X := (620891708734513/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hpowhi : (9803/50000 : ℝ) ^ (2141/512 : ℝ) ≤ (10990693293411717/10000000000000000000 : ℝ) := by
    have hpowers : (9803/50000 : ℝ)^2141 ≤ (10990693293411717/10000000000000000000 : ℝ)^512 := by
      have hnat : (9803 : ℕ)^2141*10000000000000000000^512 ≤ 10990693293411717^512*50000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9803 50000 10990693293411717 10000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9803/50000 : ℝ)) (X := (10990693293411717/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000620891708734513/25000000000000000000 : ℝ) ≤ (10000059391602309/10000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (25000620891708734513/25000000000000000000 : ℝ)^512 ≤ (10000059391602309/10000000000000000 : ℝ)^2141 := by
      have hnat : (25000620891708734513 : ℕ)^512*10000000000000000^2141 ≤ 10000059391602309^2141*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000620891708734513 25000000000000000000 10000059391602309 10000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000059391602309/10000000000000000 : ℝ)) (X := (25000620891708734513/25000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25027787179087896549/25000000000000000000 : ℝ) ≤ (312583027929799/312500000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (25027787179087896549/25000000000000000000 : ℝ)^512 ≤ (312583027929799/312500000000000 : ℝ)^2141 := by
      have hnat : (25027787179087896549 : ℕ)^512*312500000000000^2141 ≤ 312583027929799^2141*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25027787179087896549 25000000000000000000 312583027929799 312500000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312583027929799/312500000000000 : ℝ)) (X := (25027787179087896549/25000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5010990693293411717/5000000000000000000 : ℝ) ≤ (10005254395904827/10000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (5010990693293411717/5000000000000000000 : ℝ)^512 ≤ (10005254395904827/10000000000000000 : ℝ)^2141 := by
      have hnat : (5010990693293411717 : ℕ)^512*10000000000000000^2141 ≤ 10005254395904827^2141*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5010990693293411717 5000000000000000000 10005254395904827 10000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005254395904827/10000000000000000 : ℝ)) (X := (5010990693293411717/5000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(620891708734513/50000000000000000000 : ℝ) ≤ ((128915902180837576257/128950000000000000000 : ℝ)+2*(2597502151259/1289500000000000 : ℝ)*(6711/100000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (128915902180837576257/128950000000000000000 : ℝ)+2*(2597502151259/1289500000000000 : ℝ)*(6711/100000 : ℝ)=(10000059391602309/10000000000000000 : ℝ) by norm_num, show 1+2*(620891708734513/50000000000000000000 : ℝ)=(25000620891708734513/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10990693293411717/10000000000000000000 : ℝ)+(620891708734513/50000000000000000000 : ℝ) ≤ ((128915902180837576257/128950000000000000000 : ℝ)+(2597502151259/1289500000000000 : ℝ)*((9803/50000 : ℝ)+(6711/100000 : ℝ)))^(2141/512 : ℝ) := by
    rw [show (128915902180837576257/128950000000000000000 : ℝ)+(2597502151259/1289500000000000 : ℝ)*((9803/50000 : ℝ)+(6711/100000 : ℝ))=(312583027929799/312500000000000 : ℝ) by norm_num, show 1+(10990693293411717/10000000000000000000 : ℝ)+(620891708734513/50000000000000000000 : ℝ)=(25027787179087896549/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10990693293411717/10000000000000000000 : ℝ) ≤ ((128915902180837576257/128950000000000000000 : ℝ)+2*(2597502151259/1289500000000000 : ℝ)*(9803/50000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (128915902180837576257/128950000000000000000 : ℝ)+2*(2597502151259/1289500000000000 : ℝ)*(9803/50000 : ℝ)=(10005254395904827/10000000000000000 : ℝ) by norm_num, show 1+2*(10990693293411717/10000000000000000000 : ℝ)=(5010990693293411717/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (128915902180837576257/128950000000000000000 : ℝ)*(X 1 0+X 2 0)+(2597502151259/1289500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (6711/100000 : ℝ)) (hi := (9803/50000 : ℝ)) (c := (128915902180837576257/128950000000000000000 : ℝ)) (alpha := (2597502151259/1289500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (128915902180837576257/128950000000000000000 : ℝ)*(X 0 1+X 2 1)+(2597502151259/1289500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (6711/100000 : ℝ)) (hi := (9803/50000 : ℝ)) (c := (128915902180837576257/128950000000000000000 : ℝ)) (alpha := (2597502151259/1289500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (128915902180837576257/128950000000000000000 : ℝ)*(X 0 2+X 1 2)+(2597502151259/1289500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (6711/100000 : ℝ)) (hi := (9803/50000 : ℝ)) (c := (128915902180837576257/128950000000000000000 : ℝ)) (alpha := (2597502151259/1289500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2049827023/10000000000 : ℝ)*X 0 0+(685632871/1250000000 : ℝ)*X 0 1+(1294897379/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5367306763/10000000000 : ℝ)*X 1 0+(-2207836867/10000000000 : ℝ)*X 1 1+(1294897259/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536730609/1000000000 : ℝ)*X 2 0+(51795897/100000000 : ℝ)*X 2 1+(-2207836887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((864974859/2000000000 : ℝ)*X 0 0+(4018198113/10000000000 : ℝ)*X 0 1+(4653472099/10000000000 : ℝ)*X 0 2+(864974859/2000000000 : ℝ)*X 1 0+(4018198113/10000000000 : ℝ)*X 1 1+(4653472099/10000000000 : ℝ)*X 1 2+(864974859/2000000000 : ℝ)*X 2 0+(4018198113/10000000000 : ℝ)*X 2 1+(4653472099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2049898519/10000000000 : ℝ)*X 0 0+(647693241/1250000000 : ℝ)*X 0 1+(2741544381/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288735169/10000000000 : ℝ)*X 1 0+(-1904336629/10000000000 : ℝ)*X 1 1+(5483088817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330545953/625000000 : ℝ)*X 2 0+(5483088769/10000000000 : ℝ)*X 2 1+(-1904336587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081255333/2500000000 : ℝ)*X 0 0+(1162350311/2500000000 : ℝ)*X 0 1+(4022309387/10000000000 : ℝ)*X 0 2+(1081255333/2500000000 : ℝ)*X 1 0+(1162350311/2500000000 : ℝ)*X 1 1+(4022309387/10000000000 : ℝ)*X 1 2+(1081255333/2500000000 : ℝ)*X 2 0+(1162350311/2500000000 : ℝ)*X 2 1+(4022309387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91138386243903670945004637/644750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (266566969/50000000000000 : ℝ)*(base19) + (647481027/100000000000000 : ℝ)*(base23) + (99859533/100000000000000 : ℝ)*(upper3) + (292085341/100000000000000 : ℝ)*(lower4) + (537599169/100000000000000 : ℝ)*(upper5) + (242387317164447/10000000000000 : ℝ)*(major0) + (242387317164447/10000000000000 : ℝ)*(major1) + (242387317164447/10000000000000 : ℝ)*(major2) + (818400701099329/25000000000000 : ℝ)*(sp0) + (1636801135631689/50000000000000 : ℝ)*(sp1) + (818400208370807/25000000000000 : ℝ)*(sp2) + (787068341479081/50000000000000 : ℝ)*(sp3) + (661716531/50000000000000 : ℝ)*(sp6) + (3425610817/50000000000000 : ℝ)*(sp7) + (314828706835959/20000000000000 : ℝ)*(f.failure) + (818400701099329/25000000000000 : ℝ)*(f.sum) + (13731608347851/3223750000000000000000000000 : ℝ)*base66 + (8899073657594034879/1289500000000000000000000000000000 : ℝ)*base67 + (1462804964895034879/1289500000000000000000000000000000 : ℝ)*base69 + (129635000584965121/1289500000000000000000000000000000 : ℝ)*base72 + (15159015730737/6447500000000000000000000000 : ℝ)*base74 + (3572672614908965121/1289500000000000000000000000000000 : ℝ)*base76 + (12549586401123965121/1289500000000000000000000000000000 : ℝ)*base78 + (11857799446310965121/1289500000000000000000000000000000 : ℝ)*base80 + (208276990311/805937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5843061/1000000000000000000000 : ℝ)*base90 + (5843061/1000000000000000000000 : ℝ)*base92 + (5843061/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1638371480900017956494311341/805937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (95883341/20000000000000 : ℝ)*(base19) + (657171049/100000000000000 : ℝ)*(base23) + (72939089/100000000000000 : ℝ)*(upper3) + (46104631/100000000000000 : ℝ)*(lower4) + (306933777661671/12500000000000 : ℝ)*(major0) + (306933777661671/12500000000000 : ℝ)*(major1) + (306933777661671/12500000000000 : ℝ)*(major2) + (1066549047/20000000000000 : ℝ)*(sp1) + (2023860909/25000000000000 : ℝ)*(sp2) + (50565419/25000000000000 : ℝ)*(sp3) + (663255333975123/20000000000000 : ℝ)*(sp4) + (132650834308547/4000000000000 : ℝ)*(sp5) + (331626791726093/10000000000000 : ℝ)*(sp6) + (398665875671721/25000000000000 : ℝ)*(sp7) + (1594663704948559/100000000000000 : ℝ)*(f.failure) + (663255333975123/20000000000000 : ℝ)*(f.sum) + (188747337740113/64475000000000000000000000000 : ℝ)*base66 + (4574150185210054553/1611875000000000000000000000000000 : ℝ)*base68 + (4062460237573804553/1611875000000000000000000000000000 : ℝ)*base70 + (9675801427232554553/1611875000000000000000000000000000 : ℝ)*base72 + (32507602302147/16118750000000000000000000000 : ℝ)*base74 + (8794858468929320447/1611875000000000000000000000000000 : ℝ)*base75 + (345961268704945447/1611875000000000000000000000000000 : ℝ)*base77 + (241266821678804553/1611875000000000000000000000000000 : ℝ)*base80 + (232130865764969/32237500000000000000000000000 : ℝ)*base82 + (48958461/5000000000000000000000 : ℝ)*base90 + (48958461/5000000000000000000000 : ℝ)*base92 + (48958461/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1323_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9803/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6711/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (389/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16181/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1323_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1323_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (389/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16181/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1323_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1323_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1323_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (389/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16181/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1323_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
