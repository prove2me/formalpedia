-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1106_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:03:15.45714+00:00
-- url     : https://prove2.me/submissions/88d8fd9d-14f3-443e-923f-36df66a81765

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
theorem support_rectangle_w1106_s0_0 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-951628611/5000000000 : ℝ)*x 0 + (6062688403/10000000000 : ℝ)*x 1 + (2387951099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (951628611/5000000000 : ℝ)^8299 ≤ (11052002940897/100000000000000 : ℝ)^6251 := by
    have hnat : (951628611 : ℕ)^8299*100000000000000^6251 ≤ 11052002940897^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951628611 5000000000 11052002940897 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6062688403/10000000000 : ℝ)^8299 ≤ (51458887049897/100000000000000 : ℝ)^6251 := by
    have hnat : (6062688403 : ℕ)^8299*100000000000000^6251 ≤ 51458887049897^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6062688403 10000000000 51458887049897 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2387951099/5000000000 : ℝ)^8299 ≤ (18744554996923/50000000000000 : ℝ)^6251 := by
    have hnat : (2387951099 : ℕ)^8299*50000000000000^6251 ≤ 18744554996923^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387951099 5000000000 18744554996923 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-951628611/5000000000 : ℝ), (6062688403/10000000000 : ℝ), (2387951099/5000000000 : ℝ)] ![(11052002940897/100000000000000 : ℝ), (51458887049897/100000000000000 : ℝ), (18744554996923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-951628611/5000000000 : ℝ)|^8299 ≤ (11052002940897/100000000000000 : ℝ)^6251
        have hw : |(-951628611/5000000000 : ℝ)|=(951628611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6062688403/10000000000 : ℝ)|^8299 ≤ (51458887049897/100000000000000 : ℝ)^6251
        have hw : |(6062688403/10000000000 : ℝ)|=(6062688403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2387951099/5000000000 : ℝ)|^8299 ≤ (18744554996923/50000000000000 : ℝ)^6251
        have hw : |(2387951099/5000000000 : ℝ)|=(2387951099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s0_1 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5518821601/10000000000 : ℝ)*x 0 + (-264276481/1000000000 : ℝ)*x 1 + (4775902177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518821601/10000000000 : ℝ)^8299 ≤ (45422193363809/100000000000000 : ℝ)^6251 := by
    have hnat : (5518821601 : ℕ)^8299*100000000000000^6251 ≤ 45422193363809^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518821601 10000000000 45422193363809 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264276481/1000000000 : ℝ)^8299 ≤ (8544348424041/50000000000000 : ℝ)^6251 := by
    have hnat : (264276481 : ℕ)^8299*50000000000000^6251 ≤ 8544348424041^6251*1000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264276481 1000000000 8544348424041 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4775902177/10000000000 : ℝ)^8299 ≤ (37489109774997/100000000000000 : ℝ)^6251 := by
    have hnat : (4775902177 : ℕ)^8299*100000000000000^6251 ≤ 37489109774997^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4775902177 10000000000 37489109774997 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518821601/10000000000 : ℝ), (-264276481/1000000000 : ℝ), (4775902177/10000000000 : ℝ)] ![(45422193363809/100000000000000 : ℝ), (8544348424041/50000000000000 : ℝ), (37489109774997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518821601/10000000000 : ℝ)|^8299 ≤ (45422193363809/100000000000000 : ℝ)^6251
        have hw : |(5518821601/10000000000 : ℝ)|=(5518821601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-264276481/1000000000 : ℝ)|^8299 ≤ (8544348424041/50000000000000 : ℝ)^6251
        have hw : |(-264276481/1000000000 : ℝ)|=(264276481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4775902177/10000000000 : ℝ)|^8299 ≤ (37489109774997/100000000000000 : ℝ)^6251
        have hw : |(4775902177/10000000000 : ℝ)|=(4775902177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s0_2 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1379705101/2500000000 : ℝ)*x 0 + (4775903241/10000000000 : ℝ)*x 1 + (-1321382521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1379705101/2500000000 : ℝ)^8299 ≤ (22711090142139/50000000000000 : ℝ)^6251 := by
    have hnat : (1379705101 : ℕ)^8299*50000000000000^6251 ≤ 22711090142139^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379705101 2500000000 22711090142139 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4775903241/10000000000 : ℝ)^8299 ≤ (9372280215841/25000000000000 : ℝ)^6251 := by
    have hnat : (4775903241 : ℕ)^8299*25000000000000^6251 ≤ 9372280215841^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4775903241 10000000000 9372280215841 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1321382521/5000000000 : ℝ)^8299 ≤ (854434941987/5000000000000 : ℝ)^6251 := by
    have hnat : (1321382521 : ℕ)^8299*5000000000000^6251 ≤ 854434941987^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321382521 5000000000 854434941987 5000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1379705101/2500000000 : ℝ), (4775903241/10000000000 : ℝ), (-1321382521/5000000000 : ℝ)] ![(22711090142139/50000000000000 : ℝ), (9372280215841/25000000000000 : ℝ), (854434941987/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1379705101/2500000000 : ℝ)|^8299 ≤ (22711090142139/50000000000000 : ℝ)^6251
        have hw : |(1379705101/2500000000 : ℝ)|=(1379705101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4775903241/10000000000 : ℝ)|^8299 ≤ (9372280215841/25000000000000 : ℝ)^6251
        have hw : |(4775903241/10000000000 : ℝ)|=(4775903241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1321382521/5000000000 : ℝ)|^8299 ≤ (854434941987/5000000000000 : ℝ)^6251
        have hw : |(-1321382521/5000000000 : ℝ)|=(1321382521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s0_3 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4203918767/10000000000 : ℝ)*x 0 + (3122805449/10000000000 : ℝ)*x 1 + (5664768157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203918767/10000000000 : ℝ)^8299 ≤ (15824248491659/50000000000000 : ℝ)^6251 := by
    have hnat : (4203918767 : ℕ)^8299*50000000000000^6251 ≤ 15824248491659^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203918767 10000000000 15824248491659 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3122805449/10000000000 : ℝ)^8299 ≤ (16662261159/78125000000 : ℝ)^6251 := by
    have hnat : (3122805449 : ℕ)^8299*78125000000^6251 ≤ 16662261159^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122805449 10000000000 16662261159 78125000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5664768157/10000000000 : ℝ)^8299 ≤ (2938988044589/6250000000000 : ℝ)^6251 := by
    have hnat : (5664768157 : ℕ)^8299*6250000000000^6251 ≤ 2938988044589^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664768157 10000000000 2938988044589 6250000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203918767/10000000000 : ℝ), (3122805449/10000000000 : ℝ), (5664768157/10000000000 : ℝ)] ![(15824248491659/50000000000000 : ℝ), (16662261159/78125000000 : ℝ), (2938988044589/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203918767/10000000000 : ℝ)|^8299 ≤ (15824248491659/50000000000000 : ℝ)^6251
        have hw : |(4203918767/10000000000 : ℝ)|=(4203918767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3122805449/10000000000 : ℝ)|^8299 ≤ (16662261159/78125000000 : ℝ)^6251
        have hw : |(3122805449/10000000000 : ℝ)|=(3122805449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5664768157/10000000000 : ℝ)|^8299 ≤ (2938988044589/6250000000000 : ℝ)^6251
        have hw : |(5664768157/10000000000 : ℝ)|=(5664768157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s0_4 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1908510541/10000000000 : ℝ)*x 0 + (4809114543/10000000000 : ℝ)*x 1 + (3014155291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1908510541/10000000000 : ℝ)^8299 ≤ (11092521103881/100000000000000 : ℝ)^6251 := by
    have hnat : (1908510541 : ℕ)^8299*100000000000000^6251 ≤ 11092521103881^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908510541 10000000000 11092521103881 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4809114543/10000000000 : ℝ)^8299 ≤ (4729452841507/12500000000000 : ℝ)^6251 := by
    have hnat : (4809114543 : ℕ)^8299*12500000000000^6251 ≤ 4729452841507^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4809114543 10000000000 4729452841507 12500000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3014155291/5000000000 : ℝ)^8299 ≤ (25535928074951/50000000000000 : ℝ)^6251 := by
    have hnat : (3014155291 : ℕ)^8299*50000000000000^6251 ≤ 25535928074951^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3014155291 5000000000 25535928074951 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1908510541/10000000000 : ℝ), (4809114543/10000000000 : ℝ), (3014155291/5000000000 : ℝ)] ![(11092521103881/100000000000000 : ℝ), (4729452841507/12500000000000 : ℝ), (25535928074951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1908510541/10000000000 : ℝ)|^8299 ≤ (11092521103881/100000000000000 : ℝ)^6251
        have hw : |(-1908510541/10000000000 : ℝ)|=(1908510541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4809114543/10000000000 : ℝ)|^8299 ≤ (4729452841507/12500000000000 : ℝ)^6251
        have hw : |(4809114543/10000000000 : ℝ)|=(4809114543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3014155291/5000000000 : ℝ)|^8299 ≤ (25535928074951/50000000000000 : ℝ)^6251
        have hw : |(3014155291/5000000000 : ℝ)|=(3014155291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s0_5 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2584676751/5000000000 : ℝ)*x 0 + (-17379473/125000000 : ℝ)*x 1 + (1507078019/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584676751/5000000000 : ℝ)^8299 ≤ (20821884960581/50000000000000 : ℝ)^6251 := by
    have hnat : (2584676751 : ℕ)^8299*50000000000000^6251 ≤ 20821884960581^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584676751 5000000000 20821884960581 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17379473/125000000 : ℝ)^8299 ≤ (1456871422849/20000000000000 : ℝ)^6251 := by
    have hnat : (17379473 : ℕ)^8299*20000000000000^6251 ≤ 1456871422849^6251*125000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17379473 125000000 1456871422849 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1507078019/2500000000 : ℝ)^8299 ≤ (51071872953911/100000000000000 : ℝ)^6251 := by
    have hnat : (1507078019 : ℕ)^8299*100000000000000^6251 ≤ 51071872953911^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507078019 2500000000 51071872953911 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584676751/5000000000 : ℝ), (-17379473/125000000 : ℝ), (1507078019/2500000000 : ℝ)] ![(20821884960581/50000000000000 : ℝ), (1456871422849/20000000000000 : ℝ), (51071872953911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584676751/5000000000 : ℝ)|^8299 ≤ (20821884960581/50000000000000 : ℝ)^6251
        have hw : |(2584676751/5000000000 : ℝ)|=(2584676751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17379473/125000000 : ℝ)|^8299 ≤ (1456871422849/20000000000000 : ℝ)^6251
        have hw : |(-17379473/125000000 : ℝ)|=(17379473/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1507078019/2500000000 : ℝ)|^8299 ≤ (51071872953911/100000000000000 : ℝ)^6251
        have hw : |(1507078019/2500000000 : ℝ)|=(1507078019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s0_6 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2584677829/5000000000 : ℝ)*x 0 + (3014155539/5000000000 : ℝ)*x 1 + (-1390356137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584677829/5000000000 : ℝ)^8299 ≤ (10410948245019/25000000000000 : ℝ)^6251 := by
    have hnat : (2584677829 : ℕ)^8299*25000000000000^6251 ≤ 10410948245019^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584677829 5000000000 10410948245019 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3014155539/5000000000 : ℝ)^8299 ≤ (51071861728743/100000000000000 : ℝ)^6251 := by
    have hnat : (3014155539 : ℕ)^8299*100000000000000^6251 ≤ 51071861728743^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3014155539 5000000000 51071861728743 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1390356137/10000000000 : ℝ)^8299 ≤ (455271579293/6250000000000 : ℝ)^6251 := by
    have hnat : (1390356137 : ℕ)^8299*6250000000000^6251 ≤ 455271579293^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390356137 10000000000 455271579293 6250000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584677829/5000000000 : ℝ), (3014155539/5000000000 : ℝ), (-1390356137/10000000000 : ℝ)] ![(10410948245019/25000000000000 : ℝ), (51071861728743/100000000000000 : ℝ), (455271579293/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584677829/5000000000 : ℝ)|^8299 ≤ (10410948245019/25000000000000 : ℝ)^6251
        have hw : |(2584677829/5000000000 : ℝ)|=(2584677829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3014155539/5000000000 : ℝ)|^8299 ≤ (51071861728743/100000000000000 : ℝ)^6251
        have hw : |(3014155539/5000000000 : ℝ)|=(3014155539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1390356137/10000000000 : ℝ)|^8299 ≤ (455271579293/6250000000000 : ℝ)^6251
        have hw : |(-1390356137/10000000000 : ℝ)|=(1390356137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s0_7 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4214292931/10000000000 : ℝ)*x 0 + (1119832361/2000000000 : ℝ)*x 1 + (319071413/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4214292931/10000000000 : ℝ)^8299 ≤ (31752226792751/100000000000000 : ℝ)^6251 := by
    have hnat : (4214292931 : ℕ)^8299*100000000000000^6251 ≤ 31752226792751^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214292931 10000000000 31752226792751 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119832361/2000000000 : ℝ)^8299 ≤ (46302151534873/100000000000000 : ℝ)^6251 := by
    have hnat : (1119832361 : ℕ)^8299*100000000000000^6251 ≤ 46302151534873^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119832361 2000000000 46302151534873 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319071413/1000000000 : ℝ)^8299 ≤ (21945621654391/100000000000000 : ℝ)^6251 := by
    have hnat : (319071413 : ℕ)^8299*100000000000000^6251 ≤ 21945621654391^6251*1000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319071413 1000000000 21945621654391 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4214292931/10000000000 : ℝ), (1119832361/2000000000 : ℝ), (319071413/1000000000 : ℝ)] ![(31752226792751/100000000000000 : ℝ), (46302151534873/100000000000000 : ℝ), (21945621654391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4214292931/10000000000 : ℝ)|^8299 ≤ (31752226792751/100000000000000 : ℝ)^6251
        have hw : |(4214292931/10000000000 : ℝ)|=(4214292931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119832361/2000000000 : ℝ)|^8299 ≤ (46302151534873/100000000000000 : ℝ)^6251
        have hw : |(1119832361/2000000000 : ℝ)|=(1119832361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(319071413/1000000000 : ℝ)|^8299 ≤ (21945621654391/100000000000000 : ℝ)^6251
        have hw : |(319071413/1000000000 : ℝ)|=(319071413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1106_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (33/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13977/50000 : ℝ)*pair X 0 0 := by
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
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (4149/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4149 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4149*1^1024 ≤ 0^1024*1^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4149/1024 : ℝ) ≤ (2441425413500019369/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4149 ≤ (2441425413500019369/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4149*100000000000000000000^1024 ≤ 2441425413500019369^1024*5^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2441425413500019369 100000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2441425413500019369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4149 := by
      have hnat : (1 : ℕ)^1024*1^4149 ≤ 1^4149*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102441425413500019369/100000000000000000000 : ℝ) ≤ (10059709717132813/10000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (102441425413500019369/100000000000000000000 : ℝ)^1024 ≤ (10059709717132813/10000000000000000 : ℝ)^4149 := by
      have hnat : (102441425413500019369 : ℕ)^1024*10000000000000000^4149 ≤ 10059709717132813^4149*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102441425413500019369 100000000000000000000 10059709717132813 10000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059709717132813/10000000000000000 : ℝ)) (X := (102441425413500019369/100000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52441425413500019369/50000000000000000000 : ℝ) ≤ (5059709717132813/5000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (52441425413500019369/50000000000000000000 : ℝ)^1024 ≤ (5059709717132813/5000000000000000 : ℝ)^4149 := by
      have hnat : (52441425413500019369 : ℕ)^1024*5000000000000000^4149 ≤ 5059709717132813^4149*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52441425413500019369 50000000000000000000 5059709717132813 5000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059709717132813/5000000000000000 : ℝ)) (X := (52441425413500019369/50000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(59709717132813/4000000000000000 : ℝ)*(0 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(59709717132813/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2441425413500019369/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(59709717132813/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4149/1024 : ℝ) := by
    rw [show (1 : ℝ)+(59709717132813/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10059709717132813/10000000000000000 : ℝ) by norm_num, show 1+(2441425413500019369/100000000000000000000 : ℝ)+(0 : ℝ)=(102441425413500019369/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2441425413500019369/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(59709717132813/4000000000000000 : ℝ)*(2/5 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(59709717132813/4000000000000000 : ℝ)*(2/5 : ℝ)=(5059709717132813/5000000000000000 : ℝ) by norm_num, show 1+2*(2441425413500019369/100000000000000000000 : ℝ)=(52441425413500019369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(59709717132813/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59709717132813/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(59709717132813/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59709717132813/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(59709717132813/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59709717132813/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-951628611/5000000000 : ℝ)*X 0 0+(6062688403/10000000000 : ℝ)*X 0 1+(2387951099/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5518821601/10000000000 : ℝ)*X 1 0+(-264276481/1000000000 : ℝ)*X 1 1+(4775902177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1379705101/2500000000 : ℝ)*X 2 0+(4775903241/10000000000 : ℝ)*X 2 1+(-1321382521/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4203918767/10000000000 : ℝ)*X 0 0+(3122805449/10000000000 : ℝ)*X 0 1+(5664768157/10000000000 : ℝ)*X 0 2+(4203918767/10000000000 : ℝ)*X 1 0+(3122805449/10000000000 : ℝ)*X 1 1+(5664768157/10000000000 : ℝ)*X 1 2+(4203918767/10000000000 : ℝ)*X 2 0+(3122805449/10000000000 : ℝ)*X 2 1+(5664768157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1908510541/10000000000 : ℝ)*X 0 0+(4809114543/10000000000 : ℝ)*X 0 1+(3014155291/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2584676751/5000000000 : ℝ)*X 1 0+(-17379473/125000000 : ℝ)*X 1 1+(1507078019/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2584677829/5000000000 : ℝ)*X 2 0+(3014155539/5000000000 : ℝ)*X 2 1+(-1390356137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4214292931/10000000000 : ℝ)*X 0 0+(1119832361/2000000000 : ℝ)*X 0 1+(319071413/1000000000 : ℝ)*X 0 2+(4214292931/10000000000 : ℝ)*X 1 0+(1119832361/2000000000 : ℝ)*X 1 1+(319071413/1000000000 : ℝ)*X 1 2+(4214292931/10000000000 : ℝ)*X 2 0+(1119832361/2000000000 : ℝ)*X 2 1+(319071413/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (171006588125094176103171/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42850821/50000000000000 : ℝ)*(base1) + (882766609/50000000000000 : ℝ)*(base19) + (301055523/20000000000000 : ℝ)*(base23) + (18339793/20000000000000 : ℝ)*(base24) + (209451043/50000000000000 : ℝ)*(upper3) + (292635329601011/50000000000000 : ℝ)*(major0) + (292635329601011/50000000000000 : ℝ)*(major1) + (292635329601011/50000000000000 : ℝ)*(major2) + (19428396514553/2500000000000 : ℝ)*(sp0) + (777137689197101/100000000000000 : ℝ)*(sp1) + (777137857753739/100000000000000 : ℝ)*(sp2) + (39339857737019/10000000000000 : ℝ)*(sp3) + (3679849841/100000000000000 : ℝ)*(sp4) + (594518621/20000000000000 : ℝ)*(sp7) + (393401635664937/100000000000000 : ℝ)*(f.failure) + (777139454730319/100000000000000 : ℝ)*(f.sum) + (212908999673943/100000000000000000000000000000 : ℝ)*base65 + (84351814473943/200000000000000000000000000000 : ℝ)*base67 + (357431954326057/200000000000000000000000000000 : ℝ)*base70 + (319039148873943/200000000000000000000000000000 : ℝ)*base71 + (158983783573943/100000000000000000000000000000 : ℝ)*base73 + (139266285326057/200000000000000000000000000000 : ℝ)*base76 + (508016777873943/200000000000000000000000000000 : ℝ)*base77 + (302856599273943/200000000000000000000000000000 : ℝ)*base79 + (275442041873943/100000000000000000000000000000 : ℝ)*base81 + (46607833/10000000000000000000000 : ℝ)*base90 + (46607833/10000000000000000000000 : ℝ)*base92 + (46607833/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (145262116596036652987821/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1102068731/100000000000000 : ℝ)*(base19) + (1908864879/100000000000000 : ℝ)*(base23) + (106918637/25000000000000 : ℝ)*(base39) + (357678213/100000000000000 : ℝ)*(base45) + (101284041/50000000000000 : ℝ)*(upper3) + (322144299/100000000000000 : ℝ)*(upper5) + (308852924520579/50000000000000 : ℝ)*(major0) + (308852924520579/50000000000000 : ℝ)*(major1) + (61770542136661/10000000000000 : ℝ)*(major2) + (146103657/20000000000000 : ℝ)*(sp2) + (820207416860749/100000000000000 : ℝ)*(sp4) + (410103157396009/50000000000000 : ℝ)*(sp5) + (410102602576067/50000000000000 : ℝ)*(sp6) + (12975112857609/3125000000000 : ℝ)*(sp7) + (12975112857609/3125000000000 : ℝ)*(f.failure) + (820207844535297/100000000000000 : ℝ)*(f.sum) + (42930884411423/50000000000000000000000000000 : ℝ)*base65 + (40753791477393/40000000000000000000000000000 : ℝ)*base67 + (38815776941273/200000000000000000000000000000 : ℝ)*base70 + (58725481202607/40000000000000000000000000000 : ℝ)*base72 + (185874554361423/50000000000000000000000000000 : ℝ)*base73 + (262948466941273/200000000000000000000000000000 : ℝ)*base76 + (899998433341273/200000000000000000000000000000 : ℝ)*base78 + (1770645100741273/200000000000000000000000000000 : ℝ)*base80 + (96955883458727/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (157719/312500000000000000000 : ℝ)*base89 + (157719/312500000000000000000 : ℝ)*base91 + (157719/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1106_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (33/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13977/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1106_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1106_s1_0 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-527628999/2500000000 : ℝ)*x 0 + (571125167/1000000000 : ℝ)*x 1 + (4994634993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527628999/2500000000 : ℝ)^8299 ≤ (12677678560387/100000000000000 : ℝ)^6251 := by
    have hnat : (527628999 : ℕ)^8299*100000000000000^6251 ≤ 12677678560387^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527628999 2500000000 12677678560387 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571125167/1000000000 : ℝ)^8299 ≤ (2971048760077/6250000000000 : ℝ)^6251 := by
    have hnat : (571125167 : ℕ)^8299*6250000000000^6251 ≤ 2971048760077^6251*1000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571125167 1000000000 2971048760077 6250000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4994634993/10000000000 : ℝ)^8299 ≤ (39785541257333/100000000000000 : ℝ)^6251 := by
    have hnat : (4994634993 : ℕ)^8299*100000000000000^6251 ≤ 39785541257333^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4994634993 10000000000 39785541257333 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527628999/2500000000 : ℝ), (571125167/1000000000 : ℝ), (4994634993/10000000000 : ℝ)] ![(12677678560387/100000000000000 : ℝ), (2971048760077/6250000000000 : ℝ), (39785541257333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527628999/2500000000 : ℝ)|^8299 ≤ (12677678560387/100000000000000 : ℝ)^6251
        have hw : |(-527628999/2500000000 : ℝ)|=(527628999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(571125167/1000000000 : ℝ)|^8299 ≤ (2971048760077/6250000000000 : ℝ)^6251
        have hw : |(571125167/1000000000 : ℝ)|=(571125167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4994634993/10000000000 : ℝ)|^8299 ≤ (39785541257333/100000000000000 : ℝ)^6251
        have hw : |(4994634993/10000000000 : ℝ)|=(4994634993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s1_1 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1084221169/2000000000 : ℝ)*x 0 + (-624490113/2500000000 : ℝ)*x 1 + (4994635031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084221169/2000000000 : ℝ)^8299 ≤ (22178784907579/50000000000000 : ℝ)^6251 := by
    have hnat : (1084221169 : ℕ)^8299*50000000000000^6251 ≤ 22178784907579^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084221169 2000000000 22178784907579 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624490113/2500000000 : ℝ)^8299 ≤ (1585688851637/10000000000000 : ℝ)^6251 := by
    have hnat : (624490113 : ℕ)^8299*10000000000000^6251 ≤ 1585688851637^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624490113 2500000000 1585688851637 10000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4994635031/10000000000 : ℝ)^8299 ≤ (39785541659199/100000000000000 : ℝ)^6251 := by
    have hnat : (4994635031 : ℕ)^8299*100000000000000^6251 ≤ 39785541659199^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4994635031 10000000000 39785541659199 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084221169/2000000000 : ℝ), (-624490113/2500000000 : ℝ), (4994635031/10000000000 : ℝ)] ![(22178784907579/50000000000000 : ℝ), (1585688851637/10000000000000 : ℝ), (39785541659199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084221169/2000000000 : ℝ)|^8299 ≤ (22178784907579/50000000000000 : ℝ)^6251
        have hw : |(1084221169/2000000000 : ℝ)|=(1084221169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-624490113/2500000000 : ℝ)|^8299 ≤ (1585688851637/10000000000000 : ℝ)^6251
        have hw : |(-624490113/2500000000 : ℝ)|=(624490113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4994635031/10000000000 : ℝ)|^8299 ≤ (39785541659199/100000000000000 : ℝ)^6251
        have hw : |(4994635031/10000000000 : ℝ)|=(4994635031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s1_2 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1084221409/2000000000 : ℝ)*x 0 + (4994633877/10000000000 : ℝ)*x 1 + (-1248980177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084221409/2000000000 : ℝ)^8299 ≤ (44357582850949/100000000000000 : ℝ)^6251 := by
    have hnat : (1084221409 : ℕ)^8299*100000000000000^6251 ≤ 44357582850949^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084221409 2000000000 44357582850949 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4994633877/10000000000 : ℝ)^8299 ≤ (994638236379/2500000000000 : ℝ)^6251 := by
    have hnat : (4994633877 : ℕ)^8299*2500000000000^6251 ≤ 994638236379^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4994633877 10000000000 994638236379 2500000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1248980177/5000000000 : ℝ)^8299 ≤ (1982110961307/12500000000000 : ℝ)^6251 := by
    have hnat : (1248980177 : ℕ)^8299*12500000000000^6251 ≤ 1982110961307^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248980177 5000000000 1982110961307 12500000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084221409/2000000000 : ℝ), (4994633877/10000000000 : ℝ), (-1248980177/5000000000 : ℝ)] ![(44357582850949/100000000000000 : ℝ), (994638236379/2500000000000 : ℝ), (1982110961307/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084221409/2000000000 : ℝ)|^8299 ≤ (44357582850949/100000000000000 : ℝ)^6251
        have hw : |(1084221409/2000000000 : ℝ)|=(1084221409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4994633877/10000000000 : ℝ)|^8299 ≤ (994638236379/2500000000000 : ℝ)^6251
        have hw : |(4994633877/10000000000 : ℝ)|=(4994633877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1248980177/5000000000 : ℝ)|^8299 ≤ (1982110961307/12500000000000 : ℝ)^6251
        have hw : |(-1248980177/5000000000 : ℝ)|=(1248980177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s1_3 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1080117133/2500000000 : ℝ)*x 0 + (3670208569/10000000000 : ℝ)*x 1 + (79466207/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080117133/2500000000 : ℝ)^8299 ≤ (2051165565199/6250000000000 : ℝ)^6251 := by
    have hnat : (1080117133 : ℕ)^8299*6250000000000^6251 ≤ 2051165565199^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080117133 2500000000 2051165565199 6250000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3670208569/10000000000 : ℝ)^8299 ≤ (6607108456807/25000000000000 : ℝ)^6251 := by
    have hnat : (3670208569 : ℕ)^8299*25000000000000^6251 ≤ 6607108456807^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3670208569 10000000000 6607108456807 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79466207/156250000 : ℝ)^8299 ≤ (20376458551987/50000000000000 : ℝ)^6251 := by
    have hnat : (79466207 : ℕ)^8299*50000000000000^6251 ≤ 20376458551987^6251*156250000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79466207 156250000 20376458551987 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080117133/2500000000 : ℝ), (3670208569/10000000000 : ℝ), (79466207/156250000 : ℝ)] ![(2051165565199/6250000000000 : ℝ), (6607108456807/25000000000000 : ℝ), (20376458551987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080117133/2500000000 : ℝ)|^8299 ≤ (2051165565199/6250000000000 : ℝ)^6251
        have hw : |(1080117133/2500000000 : ℝ)|=(1080117133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3670208569/10000000000 : ℝ)|^8299 ≤ (6607108456807/25000000000000 : ℝ)^6251
        have hw : |(3670208569/10000000000 : ℝ)|=(3670208569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79466207/156250000 : ℝ)|^8299 ≤ (20376458551987/50000000000000 : ℝ)^6251
        have hw : |(79466207/156250000 : ℝ)|=(79466207/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s1_4 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1055686897/5000000000 : ℝ)*x 0 + (1000911093/2000000000 : ℝ)*x 1 + (2850566201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055686897/5000000000 : ℝ)^8299 ≤ (6342259951143/50000000000000 : ℝ)^6251 := by
    have hnat : (1055686897 : ℕ)^8299*50000000000000^6251 ≤ 6342259951143^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055686897 5000000000 6342259951143 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000911093/2000000000 : ℝ)^8299 ≤ (39890488573701/100000000000000 : ℝ)^6251 := by
    have hnat : (1000911093 : ℕ)^8299*100000000000000^6251 ≤ 39890488573701^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000911093 2000000000 39890488573701 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2850566201/5000000000 : ℝ)^8299 ≤ (5928123939067/12500000000000 : ℝ)^6251 := by
    have hnat : (2850566201 : ℕ)^8299*12500000000000^6251 ≤ 5928123939067^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850566201 5000000000 5928123939067 12500000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1055686897/5000000000 : ℝ), (1000911093/2000000000 : ℝ), (2850566201/5000000000 : ℝ)] ![(6342259951143/50000000000000 : ℝ), (39890488573701/100000000000000 : ℝ), (5928123939067/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1055686897/5000000000 : ℝ)|^8299 ≤ (6342259951143/50000000000000 : ℝ)^6251
        have hw : |(-1055686897/5000000000 : ℝ)|=(1055686897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1000911093/2000000000 : ℝ)|^8299 ≤ (39890488573701/100000000000000 : ℝ)^6251
        have hw : |(1000911093/2000000000 : ℝ)|=(1000911093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2850566201/5000000000 : ℝ)|^8299 ≤ (5928123939067/12500000000000 : ℝ)^6251
        have hw : |(2850566201/5000000000 : ℝ)|=(2850566201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s1_5 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5237712983/10000000000 : ℝ)*x 0 + (-358292549/2000000000 : ℝ)*x 1 + (5701132217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5237712983/10000000000 : ℝ)^8299 ≤ (42376469335093/100000000000000 : ℝ)^6251 := by
    have hnat : (5237712983 : ℕ)^8299*100000000000000^6251 ≤ 42376469335093^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237712983 10000000000 42376469335093 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (358292549/2000000000 : ℝ)^8299 ≤ (10198541182039/100000000000000 : ℝ)^6251 := by
    have hnat : (358292549 : ℕ)^8299*100000000000000^6251 ≤ 10198541182039^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358292549 2000000000 10198541182039 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5701132217/10000000000 : ℝ)^8299 ≤ (9484997893883/20000000000000 : ℝ)^6251 := by
    have hnat : (5701132217 : ℕ)^8299*20000000000000^6251 ≤ 9484997893883^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5701132217 10000000000 9484997893883 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5237712983/10000000000 : ℝ), (-358292549/2000000000 : ℝ), (5701132217/10000000000 : ℝ)] ![(42376469335093/100000000000000 : ℝ), (10198541182039/100000000000000 : ℝ), (9484997893883/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5237712983/10000000000 : ℝ)|^8299 ≤ (42376469335093/100000000000000 : ℝ)^6251
        have hw : |(5237712983/10000000000 : ℝ)|=(5237712983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-358292549/2000000000 : ℝ)|^8299 ≤ (10198541182039/100000000000000 : ℝ)^6251
        have hw : |(-358292549/2000000000 : ℝ)|=(358292549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5701132217/10000000000 : ℝ)|^8299 ≤ (9484997893883/20000000000000 : ℝ)^6251
        have hw : |(5701132217/10000000000 : ℝ)|=(5701132217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s1_6 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (327357063/625000000 : ℝ)*x 0 + (2850566177/5000000000 : ℝ)*x 1 + (-1791462509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327357063/625000000 : ℝ)^8299 ≤ (42376469603627/100000000000000 : ℝ)^6251 := by
    have hnat : (327357063 : ℕ)^8299*100000000000000^6251 ≤ 42376469603627^6251*625000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327357063 625000000 42376469603627 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2850566177/5000000000 : ℝ)^8299 ≤ (47424990982429/100000000000000 : ℝ)^6251 := by
    have hnat : (2850566177 : ℕ)^8299*100000000000000^6251 ≤ 47424990982429^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850566177 5000000000 47424990982429 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1791462509/10000000000 : ℝ)^8299 ≤ (10198539398353/100000000000000 : ℝ)^6251 := by
    have hnat : (1791462509 : ℕ)^8299*100000000000000^6251 ≤ 10198539398353^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791462509 10000000000 10198539398353 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327357063/625000000 : ℝ), (2850566177/5000000000 : ℝ), (-1791462509/10000000000 : ℝ)] ![(42376469603627/100000000000000 : ℝ), (47424990982429/100000000000000 : ℝ), (10198539398353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327357063/625000000 : ℝ)|^8299 ≤ (42376469603627/100000000000000 : ℝ)^6251
        have hw : |(327357063/625000000 : ℝ)|=(327357063/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2850566177/5000000000 : ℝ)|^8299 ≤ (47424990982429/100000000000000 : ℝ)^6251
        have hw : |(2850566177/5000000000 : ℝ)|=(2850566177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1791462509/10000000000 : ℝ)|^8299 ≤ (10198539398353/100000000000000 : ℝ)^6251
        have hw : |(-1791462509/10000000000 : ℝ)|=(1791462509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s1_7 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4220861/9765625 : ℝ)*x 0 + (1266560183/2500000000 : ℝ)*x 1 + (738039543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4220861/9765625 : ℝ)^8299 ≤ (6567144998159/20000000000000 : ℝ)^6251 := by
    have hnat : (4220861 : ℕ)^8299*20000000000000^6251 ≤ 6567144998159^6251*9765625^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220861 9765625 6567144998159 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1266560183/2500000000 : ℝ)^8299 ≤ (2027228752903/5000000000000 : ℝ)^6251 := by
    have hnat : (1266560183 : ℕ)^8299*5000000000000^6251 ≤ 2027228752903^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266560183 2500000000 2027228752903 5000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (738039543/2000000000 : ℝ)^8299 ≤ (166373124577/625000000000 : ℝ)^6251 := by
    have hnat : (738039543 : ℕ)^8299*625000000000^6251 ≤ 166373124577^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738039543 2000000000 166373124577 625000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4220861/9765625 : ℝ), (1266560183/2500000000 : ℝ), (738039543/2000000000 : ℝ)] ![(6567144998159/20000000000000 : ℝ), (2027228752903/5000000000000 : ℝ), (166373124577/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4220861/9765625 : ℝ)|^8299 ≤ (6567144998159/20000000000000 : ℝ)^6251
        have hw : |(4220861/9765625 : ℝ)|=(4220861/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1266560183/2500000000 : ℝ)|^8299 ≤ (2027228752903/5000000000000 : ℝ)^6251
        have hw : |(1266560183/2500000000 : ℝ)|=(1266560183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(738039543/2000000000 : ℝ)|^8299 ≤ (166373124577/625000000000 : ℝ)^6251
        have hw : |(738039543/2000000000 : ℝ)|=(738039543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1106_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13977/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (33/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1089/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20603/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13977/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (33/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13977/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (33/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13977/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (33/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13977/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (33/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13977/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (33/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13977/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (33/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (33/12500 : ℝ) ^ (4149/1024 : ℝ) ≤ (1786214339/50000000000000000000 : ℝ) := by
    have hpowers : (33/12500 : ℝ)^4149 ≤ (1786214339/50000000000000000000 : ℝ)^1024 := by
      have hnat : (33 : ℕ)^4149*50000000000000000000^1024 ≤ 1786214339^1024*12500^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33 12500 1786214339 50000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33/12500 : ℝ)) (X := (1786214339/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13977/50000 : ℝ) ^ (4149/1024 : ℝ) ≤ (571643136752927303/100000000000000000000 : ℝ) := by
    have hpowers : (13977/50000 : ℝ)^4149 ≤ (571643136752927303/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13977 : ℕ)^4149*100000000000000000000^1024 ≤ 571643136752927303^1024*50000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13977 50000 571643136752927303 100000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13977/50000 : ℝ)) (X := (571643136752927303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000001786214339/25000000000000000000 : ℝ) ≤ (500000000008817/500000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (25000000001786214339/25000000000000000000 : ℝ)^1024 ≤ (500000000008817/500000000000000 : ℝ)^4149 := by
      have hnat : (25000000001786214339 : ℕ)^1024*500000000000000^4149 ≤ 500000000008817^4149*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000001786214339 25000000000000000000 500000000008817 500000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000000008817/500000000000000 : ℝ)) (X := (25000000001786214339/25000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100571643140325355981/100000000000000000000 : ℝ) ≤ (2002815650067581/2000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (100571643140325355981/100000000000000000000 : ℝ)^1024 ≤ (2002815650067581/2000000000000000 : ℝ)^4149 := by
      have hnat : (100571643140325355981 : ℕ)^1024*2000000000000000^4149 ≤ 2002815650067581^4149*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100571643140325355981 100000000000000000000 2002815650067581 2000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002815650067581/2000000000000000 : ℝ)) (X := (100571643140325355981/100000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50571643136752927303/50000000000000000000 : ℝ) ≤ (1002815650049947/1000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (50571643136752927303/50000000000000000000 : ℝ)^1024 ≤ (1002815650049947/1000000000000000 : ℝ)^4149 := by
      have hnat : (50571643136752927303 : ℕ)^1024*1000000000000000^4149 ≤ 1002815650049947^4149*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50571643136752927303 50000000000000000000 1002815650049947 1000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002815650049947/1000000000000000 : ℝ)) (X := (50571643136752927303/50000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1786214339/50000000000000000000 : ℝ) ≤ ((2307438055739979569/2307500000000000000 : ℝ)+2*(938550010771/184600000000000 : ℝ)*(33/12500 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (2307438055739979569/2307500000000000000 : ℝ)+2*(938550010771/184600000000000 : ℝ)*(33/12500 : ℝ)=(500000000008817/500000000000000 : ℝ) by norm_num, show 1+2*(1786214339/50000000000000000000 : ℝ)=(25000000001786214339/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(571643136752927303/100000000000000000000 : ℝ)+(1786214339/50000000000000000000 : ℝ) ≤ ((2307438055739979569/2307500000000000000 : ℝ)+(938550010771/184600000000000 : ℝ)*((13977/50000 : ℝ)+(33/12500 : ℝ)))^(4149/1024 : ℝ) := by
    rw [show (2307438055739979569/2307500000000000000 : ℝ)+(938550010771/184600000000000 : ℝ)*((13977/50000 : ℝ)+(33/12500 : ℝ))=(2002815650067581/2000000000000000 : ℝ) by norm_num, show 1+(571643136752927303/100000000000000000000 : ℝ)+(1786214339/50000000000000000000 : ℝ)=(100571643140325355981/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(571643136752927303/100000000000000000000 : ℝ) ≤ ((2307438055739979569/2307500000000000000 : ℝ)+2*(938550010771/184600000000000 : ℝ)*(13977/50000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (2307438055739979569/2307500000000000000 : ℝ)+2*(938550010771/184600000000000 : ℝ)*(13977/50000 : ℝ)=(1002815650049947/1000000000000000 : ℝ) by norm_num, show 1+2*(571643136752927303/100000000000000000000 : ℝ)=(50571643136752927303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2307438055739979569/2307500000000000000 : ℝ)*(X 1 0+X 2 0)+(938550010771/184600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (33/12500 : ℝ)) (hi := (13977/50000 : ℝ)) (c := (2307438055739979569/2307500000000000000 : ℝ)) (alpha := (938550010771/184600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2307438055739979569/2307500000000000000 : ℝ)*(X 0 1+X 2 1)+(938550010771/184600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (33/12500 : ℝ)) (hi := (13977/50000 : ℝ)) (c := (2307438055739979569/2307500000000000000 : ℝ)) (alpha := (938550010771/184600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2307438055739979569/2307500000000000000 : ℝ)*(X 0 2+X 1 2)+(938550010771/184600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (33/12500 : ℝ)) (hi := (13977/50000 : ℝ)) (c := (2307438055739979569/2307500000000000000 : ℝ)) (alpha := (938550010771/184600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-527628999/2500000000 : ℝ)*X 0 0+(571125167/1000000000 : ℝ)*X 0 1+(4994634993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1084221169/2000000000 : ℝ)*X 1 0+(-624490113/2500000000 : ℝ)*X 1 1+(4994635031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1084221409/2000000000 : ℝ)*X 2 0+(4994633877/10000000000 : ℝ)*X 2 1+(-1248980177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1080117133/2500000000 : ℝ)*X 0 0+(3670208569/10000000000 : ℝ)*X 0 1+(79466207/156250000 : ℝ)*X 0 2+(1080117133/2500000000 : ℝ)*X 1 0+(3670208569/10000000000 : ℝ)*X 1 1+(79466207/156250000 : ℝ)*X 1 2+(1080117133/2500000000 : ℝ)*X 2 0+(3670208569/10000000000 : ℝ)*X 2 1+(79466207/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1055686897/5000000000 : ℝ)*X 0 0+(1000911093/2000000000 : ℝ)*X 0 1+(2850566201/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5237712983/10000000000 : ℝ)*X 1 0+(-358292549/2000000000 : ℝ)*X 1 1+(5701132217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((327357063/625000000 : ℝ)*X 2 0+(2850566177/5000000000 : ℝ)*X 2 1+(-1791462509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4220861/9765625 : ℝ)*X 0 0+(1266560183/2500000000 : ℝ)*X 0 1+(738039543/2000000000 : ℝ)*X 0 2+(4220861/9765625 : ℝ)*X 1 0+(1266560183/2500000000 : ℝ)*X 1 1+(738039543/2000000000 : ℝ)*X 1 2+(4220861/9765625 : ℝ)*X 2 0+(1266560183/2500000000 : ℝ)*X 2 1+(738039543/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (965930958449266298997954267/115375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62601747/25000000000000 : ℝ)*(base1) + (811900949/50000000000000 : ℝ)*(base19) + (1932696507/100000000000000 : ℝ)*(base23) + (26547001/25000000000000 : ℝ)*(upper3) + (111676883/50000000000000 : ℝ)*(upper5) + (1050933717785973/100000000000000 : ℝ)*(major0) + (1050933717785973/100000000000000 : ℝ)*(major1) + (1050933717785973/100000000000000 : ℝ)*(major2) + (1395452522926547/100000000000000 : ℝ)*(sp0) + (1395458954731281/100000000000000 : ℝ)*(sp1) + (10902020670599/781250000000 : ℝ)*(sp2) + (141280635565263/20000000000000 : ℝ)*(sp3) + (415300681/5000000000000 : ℝ)*(sp4) + (1574867741/50000000000000 : ℝ)*(sp7) + (141281315593757/20000000000000 : ℝ)*(f.failure) + (1395460578533179/100000000000000 : ℝ)*(f.sum) + (23973245737903/9230000000000000000000000000 : ℝ)*base65 + (376525928467823137/230750000000000000000000000000000 : ℝ)*base67 + (475629289473823137/230750000000000000000000000000000 : ℝ)*base69 + (1493873679779823137/230750000000000000000000000000000 : ℝ)*base71 + (28703153528627/9230000000000000000000000000 : ℝ)*base74 + (2223807372748823137/230750000000000000000000000000000 : ℝ)*base75 + (417397979333573137/230750000000000000000000000000000 : ℝ)*base77 + (3190840485632323137/230750000000000000000000000000000 : ℝ)*base79 + (4720436701077/9230000000000000000000000000 : ℝ)*base82 + (2691213/2000000000000000000000 : ℝ)*base90 + (2691213/2000000000000000000000 : ℝ)*base92 + (2691213/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1012057156919432903544084567/115375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51115703/50000000000000 : ℝ)*(base1) + (1949271779/100000000000000 : ℝ)*(base19) + (1972648409/100000000000000 : ℝ)*(base23) + (197647443/100000000000000 : ℝ)*(upper3) + (39836563/20000000000000 : ℝ)*(upper5) + (1081156728690019/100000000000000 : ℝ)*(major0) + (1081156728690019/100000000000000 : ℝ)*(major1) + (1081156728690019/100000000000000 : ℝ)*(major2) + (7862406399/100000000000000 : ℝ)*(sp1) + (4167146259/50000000000000 : ℝ)*(sp2) + (717795837376307/50000000000000 : ℝ)*(sp4) + (358895440210757/25000000000000 : ℝ)*(sp5) + (35889531639507/2500000000000 : ℝ)*(sp6) + (90840186278873/12500000000000 : ℝ)*(sp7) + (72672159246239/10000000000000 : ℝ)*(f.failure) + (1435591572521207/100000000000000 : ℝ)*(f.sum) + (351415486849/9230000000000000000000000000 : ℝ)*base65 + (893151102761165689/230750000000000000000000000000000 : ℝ)*base68 + (420996126903665689/230750000000000000000000000000000 : ℝ)*base70 + (1937930740936084311/230750000000000000000000000000000 : ℝ)*base71 + (51367193223751/9230000000000000000000000000 : ℝ)*base74 + (1562300672973584311/230750000000000000000000000000000 : ℝ)*base75 + (673435307952834311/230750000000000000000000000000000 : ℝ)*base77 + (213046884236834311/230750000000000000000000000000000 : ℝ)*base79 + (6194941780991/9230000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (3955951/1000000000000000000000 : ℝ)*base90 + (3955951/1000000000000000000000 : ℝ)*base92 + (3955951/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1106_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13977/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (33/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1089/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20603/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1106_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1106_s2_0 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-541426657/2500000000 : ℝ)*x 0 + (5517813739/10000000000 : ℝ)*x 1 + (2576507859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541426657/2500000000 : ℝ)^8299 ≤ (3279923751843/25000000000000 : ℝ)^6251 := by
    have hnat : (541426657 : ℕ)^8299*25000000000000^6251 ≤ 3279923751843^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541426657 2500000000 3279923751843 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5517813739/10000000000 : ℝ)^8299 ≤ (45411180859537/100000000000000 : ℝ)^6251 := by
    have hnat : (5517813739 : ℕ)^8299*100000000000000^6251 ≤ 45411180859537^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517813739 10000000000 45411180859537 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576507859/5000000000 : ℝ)^8299 ≤ (41469124117567/100000000000000 : ℝ)^6251 := by
    have hnat : (2576507859 : ℕ)^8299*100000000000000^6251 ≤ 41469124117567^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576507859 5000000000 41469124117567 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-541426657/2500000000 : ℝ), (5517813739/10000000000 : ℝ), (2576507859/5000000000 : ℝ)] ![(3279923751843/25000000000000 : ℝ), (45411180859537/100000000000000 : ℝ), (41469124117567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-541426657/2500000000 : ℝ)|^8299 ≤ (3279923751843/25000000000000 : ℝ)^6251
        have hw : |(-541426657/2500000000 : ℝ)|=(541426657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5517813739/10000000000 : ℝ)|^8299 ≤ (45411180859537/100000000000000 : ℝ)^6251
        have hw : |(5517813739/10000000000 : ℝ)|=(5517813739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576507859/5000000000 : ℝ)|^8299 ≤ (41469124117567/100000000000000 : ℝ)^6251
        have hw : |(2576507859/5000000000 : ℝ)|=(2576507859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s2_1 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1075086163/2000000000 : ℝ)*x 0 + (-2355638273/10000000000 : ℝ)*x 1 + (5153016911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075086163/2000000000 : ℝ)^8299 ≤ (43862080833917/100000000000000 : ℝ)^6251 := by
    have hnat : (1075086163 : ℕ)^8299*100000000000000^6251 ≤ 43862080833917^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075086163 2000000000 43862080833917 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2355638273/10000000000 : ℝ)^8299 ≤ (7334391143333/50000000000000 : ℝ)^6251 := by
    have hnat : (2355638273 : ℕ)^8299*50000000000000^6251 ≤ 7334391143333^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2355638273 10000000000 7334391143333 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5153016911/10000000000 : ℝ)^8299 ≤ (41469136863749/100000000000000 : ℝ)^6251 := by
    have hnat : (5153016911 : ℕ)^8299*100000000000000^6251 ≤ 41469136863749^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153016911 10000000000 41469136863749 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075086163/2000000000 : ℝ), (-2355638273/10000000000 : ℝ), (5153016911/10000000000 : ℝ)] ![(43862080833917/100000000000000 : ℝ), (7334391143333/50000000000000 : ℝ), (41469136863749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075086163/2000000000 : ℝ)|^8299 ≤ (43862080833917/100000000000000 : ℝ)^6251
        have hw : |(1075086163/2000000000 : ℝ)|=(1075086163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2355638273/10000000000 : ℝ)|^8299 ≤ (7334391143333/50000000000000 : ℝ)^6251
        have hw : |(-2355638273/10000000000 : ℝ)|=(2355638273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5153016911/10000000000 : ℝ)|^8299 ≤ (41469136863749/100000000000000 : ℝ)^6251
        have hw : |(5153016911/10000000000 : ℝ)|=(5153016911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s2_2 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5375430767/10000000000 : ℝ)*x 0 + (1288254241/2500000000 : ℝ)*x 1 + (-588909567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375430767/10000000000 : ℝ)^8299 ≤ (5482760039241/12500000000000 : ℝ)^6251 := by
    have hnat : (5375430767 : ℕ)^8299*12500000000000^6251 ≤ 5482760039241^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375430767 10000000000 5482760039241 12500000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1288254241/2500000000 : ℝ)^8299 ≤ (41469137430009/100000000000000 : ℝ)^6251 := by
    have hnat : (1288254241 : ℕ)^8299*100000000000000^6251 ≤ 41469137430009^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288254241 2500000000 41469137430009 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (588909567/2500000000 : ℝ)^8299 ≤ (1466878224533/10000000000000 : ℝ)^6251 := by
    have hnat : (588909567 : ℕ)^8299*10000000000000^6251 ≤ 1466878224533^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588909567 2500000000 1466878224533 10000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375430767/10000000000 : ℝ), (1288254241/2500000000 : ℝ), (-588909567/2500000000 : ℝ)] ![(5482760039241/12500000000000 : ℝ), (41469137430009/100000000000000 : ℝ), (1466878224533/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375430767/10000000000 : ℝ)|^8299 ≤ (5482760039241/12500000000000 : ℝ)^6251
        have hw : |(5375430767/10000000000 : ℝ)|=(5375430767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1288254241/2500000000 : ℝ)|^8299 ≤ (41469137430009/100000000000000 : ℝ)^6251
        have hw : |(1288254241/2500000000 : ℝ)|=(1288254241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-588909567/2500000000 : ℝ)|^8299 ≤ (1466878224533/10000000000000 : ℝ)^6251
        have hw : |(-588909567/2500000000 : ℝ)|=(588909567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s2_3 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358237129/10000000000 : ℝ)*x 0 + (2006402057/5000000000 : ℝ)*x 1 + (4733436667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358237129/10000000000 : ℝ)^8299 ≤ (33200081139229/100000000000000 : ℝ)^6251 := by
    have hnat : (4358237129 : ℕ)^8299*100000000000000^6251 ≤ 33200081139229^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358237129 10000000000 33200081139229 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006402057/5000000000 : ℝ)^8299 ≤ (371908914247/1250000000000 : ℝ)^6251 := by
    have hnat : (2006402057 : ℕ)^8299*1250000000000^6251 ≤ 371908914247^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006402057 5000000000 371908914247 1250000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4733436667/10000000000 : ℝ)^8299 ≤ (2315450356263/6250000000000 : ℝ)^6251 := by
    have hnat : (4733436667 : ℕ)^8299*6250000000000^6251 ≤ 2315450356263^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4733436667 10000000000 2315450356263 6250000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358237129/10000000000 : ℝ), (2006402057/5000000000 : ℝ), (4733436667/10000000000 : ℝ)] ![(33200081139229/100000000000000 : ℝ), (371908914247/1250000000000 : ℝ), (2315450356263/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358237129/10000000000 : ℝ)|^8299 ≤ (33200081139229/100000000000000 : ℝ)^6251
        have hw : |(4358237129/10000000000 : ℝ)|=(4358237129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2006402057/5000000000 : ℝ)|^8299 ≤ (371908914247/1250000000000 : ℝ)^6251
        have hw : |(2006402057/5000000000 : ℝ)|=(2006402057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4733436667/10000000000 : ℝ)|^8299 ≤ (2315450356263/6250000000000 : ℝ)^6251
        have hw : |(4733436667/10000000000 : ℝ)|=(4733436667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s2_4 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2165819457/10000000000 : ℝ)*x 0 + (5155596029/10000000000 : ℝ)*x 1 + (5515207147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165819457/10000000000 : ℝ)^8299 ≤ (13120602461801/100000000000000 : ℝ)^6251 := by
    have hnat : (2165819457 : ℕ)^8299*100000000000000^6251 ≤ 13120602461801^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165819457 10000000000 13120602461801 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5155596029/10000000000 : ℝ)^8299 ≤ (10374173697107/25000000000000 : ℝ)^6251 := by
    have hnat : (5155596029 : ℕ)^8299*25000000000000^6251 ≤ 10374173697107^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5155596029 10000000000 10374173697107 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5515207147/10000000000 : ℝ)^8299 ≤ (45382702729413/100000000000000 : ℝ)^6251 := by
    have hnat : (5515207147 : ℕ)^8299*100000000000000^6251 ≤ 45382702729413^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515207147 10000000000 45382702729413 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2165819457/10000000000 : ℝ), (5155596029/10000000000 : ℝ), (5515207147/10000000000 : ℝ)] ![(13120602461801/100000000000000 : ℝ), (10374173697107/25000000000000 : ℝ), (45382702729413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2165819457/10000000000 : ℝ)|^8299 ≤ (13120602461801/100000000000000 : ℝ)^6251
        have hw : |(-2165819457/10000000000 : ℝ)|=(2165819457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5155596029/10000000000 : ℝ)|^8299 ≤ (10374173697107/25000000000000 : ℝ)^6251
        have hw : |(5155596029/10000000000 : ℝ)|=(5155596029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5515207147/10000000000 : ℝ)|^8299 ≤ (45382702729413/100000000000000 : ℝ)^6251
        have hw : |(5515207147/10000000000 : ℝ)|=(5515207147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s2_5 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1320774127/2500000000 : ℝ)*x 0 + (-1993447459/10000000000 : ℝ)*x 1 + (5515207233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320774127/2500000000 : ℝ)^8299 ≤ (8572928157079/20000000000000 : ℝ)^6251 := by
    have hnat : (1320774127 : ℕ)^8299*20000000000000^6251 ≤ 8572928157079^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320774127 2500000000 8572928157079 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1993447459/10000000000 : ℝ)^8299 ≤ (11752655532119/100000000000000 : ℝ)^6251 := by
    have hnat : (1993447459 : ℕ)^8299*100000000000000^6251 ≤ 11752655532119^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993447459 10000000000 11752655532119 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5515207233/10000000000 : ℝ)^8299 ≤ (45382703668927/100000000000000 : ℝ)^6251 := by
    have hnat : (5515207233 : ℕ)^8299*100000000000000^6251 ≤ 45382703668927^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515207233 10000000000 45382703668927 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320774127/2500000000 : ℝ), (-1993447459/10000000000 : ℝ), (5515207233/10000000000 : ℝ)] ![(8572928157079/20000000000000 : ℝ), (11752655532119/100000000000000 : ℝ), (45382703668927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320774127/2500000000 : ℝ)|^8299 ≤ (8572928157079/20000000000000 : ℝ)^6251
        have hw : |(1320774127/2500000000 : ℝ)|=(1320774127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1993447459/10000000000 : ℝ)|^8299 ≤ (11752655532119/100000000000000 : ℝ)^6251
        have hw : |(-1993447459/10000000000 : ℝ)|=(1993447459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5515207233/10000000000 : ℝ)|^8299 ≤ (45382703668927/100000000000000 : ℝ)^6251
        have hw : |(5515207233/10000000000 : ℝ)|=(5515207233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s2_6 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2641548327/5000000000 : ℝ)*x 0 + (1378801793/2500000000 : ℝ)*x 1 + (-1993447343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641548327/5000000000 : ℝ)^8299 ≤ (42864642358073/100000000000000 : ℝ)^6251 := by
    have hnat : (2641548327 : ℕ)^8299*100000000000000^6251 ≤ 42864642358073^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641548327 5000000000 42864642358073 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1378801793/2500000000 : ℝ)^8299 ≤ (1418209468829/3125000000000 : ℝ)^6251 := by
    have hnat : (1378801793 : ℕ)^8299*3125000000000^6251 ≤ 1418209468829^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378801793 2500000000 1418209468829 3125000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1993447343/10000000000 : ℝ)^8299 ≤ (5876327312081/50000000000000 : ℝ)^6251 := by
    have hnat : (1993447343 : ℕ)^8299*50000000000000^6251 ≤ 5876327312081^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993447343 10000000000 5876327312081 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641548327/5000000000 : ℝ), (1378801793/2500000000 : ℝ), (-1993447343/10000000000 : ℝ)] ![(42864642358073/100000000000000 : ℝ), (1418209468829/3125000000000 : ℝ), (5876327312081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641548327/5000000000 : ℝ)|^8299 ≤ (42864642358073/100000000000000 : ℝ)^6251
        have hw : |(2641548327/5000000000 : ℝ)|=(2641548327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1378801793/2500000000 : ℝ)|^8299 ≤ (1418209468829/3125000000000 : ℝ)^6251
        have hw : |(1378801793/2500000000 : ℝ)|=(1378801793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1993447343/10000000000 : ℝ)|^8299 ≤ (5876327312081/50000000000000 : ℝ)^6251
        have hw : |(-1993447343/10000000000 : ℝ)|=(1993447343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s2_7 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358461339/10000000000 : ℝ)*x 0 + (2364170219/5000000000 : ℝ)*x 1 + (2008975657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358461339/10000000000 : ℝ)^8299 ≤ (33202348722233/100000000000000 : ℝ)^6251 := by
    have hnat : (4358461339 : ℕ)^8299*100000000000000^6251 ≤ 33202348722233^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358461339 10000000000 33202348722233 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2364170219/5000000000 : ℝ)^8299 ≤ (36994260393903/100000000000000 : ℝ)^6251 := by
    have hnat : (2364170219 : ℕ)^8299*100000000000000^6251 ≤ 36994260393903^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364170219 5000000000 36994260393903 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008975657/5000000000 : ℝ)^8299 ≤ (29803390868629/100000000000000 : ℝ)^6251 := by
    have hnat : (2008975657 : ℕ)^8299*100000000000000^6251 ≤ 29803390868629^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008975657 5000000000 29803390868629 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358461339/10000000000 : ℝ), (2364170219/5000000000 : ℝ), (2008975657/5000000000 : ℝ)] ![(33202348722233/100000000000000 : ℝ), (36994260393903/100000000000000 : ℝ), (29803390868629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358461339/10000000000 : ℝ)|^8299 ≤ (33202348722233/100000000000000 : ℝ)^6251
        have hw : |(4358461339/10000000000 : ℝ)|=(4358461339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2364170219/5000000000 : ℝ)|^8299 ≤ (36994260393903/100000000000000 : ℝ)^6251
        have hw : |(2364170219/5000000000 : ℝ)|=(2364170219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2008975657/5000000000 : ℝ)|^8299 ≤ (29803390868629/100000000000000 : ℝ)^6251
        have hw : |(2008975657/5000000000 : ℝ)|=(2008975657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1106_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20603/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1089/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1113/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16613/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20603/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1089/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20603/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1089/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20603/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1089/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20603/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1089/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20603/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1089/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20603/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1089/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1089/20000 : ℝ) ^ (4149/1024 : ℝ) ≤ (756083136646027/100000000000000000000 : ℝ) := by
    have hpowers : (1089/20000 : ℝ)^4149 ≤ (756083136646027/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1089 : ℕ)^4149*100000000000000000000^1024 ≤ 756083136646027^1024*20000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1089 20000 756083136646027 100000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1089/20000 : ℝ)) (X := (756083136646027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20603/100000 : ℝ) ^ (4149/1024 : ℝ) ≤ (41509968166533351/25000000000000000000 : ℝ) := by
    have hpowers : (20603/100000 : ℝ)^4149 ≤ (41509968166533351/25000000000000000000 : ℝ)^1024 := by
      have hnat : (20603 : ℕ)^4149*25000000000000000000^1024 ≤ 41509968166533351^1024*100000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20603 100000 41509968166533351 25000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20603/100000 : ℝ)) (X := (41509968166533351/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000756083136646027/50000000000000000000 : ℝ) ≤ (5000018660513929/5000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (50000756083136646027/50000000000000000000 : ℝ)^1024 ≤ (5000018660513929/5000000000000000 : ℝ)^4149 := by
      have hnat : (50000756083136646027 : ℕ)^1024*5000000000000000^4149 ≤ 5000018660513929^4149*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000756083136646027 50000000000000000000 5000018660513929 5000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000018660513929/5000000000000000 : ℝ)) (X := (50000756083136646027/50000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100166795955802779431/100000000000000000000 : ℝ) ≤ (5002057024296001/5000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (100166795955802779431/100000000000000000000 : ℝ)^1024 ≤ (5002057024296001/5000000000000000 : ℝ)^4149 := by
      have hnat : (100166795955802779431 : ℕ)^1024*5000000000000000^4149 ≤ 5002057024296001^4149*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100166795955802779431 100000000000000000000 5002057024296001 5000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002057024296001/5000000000000000 : ℝ)) (X := (100166795955802779431/100000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12541509968166533351/12500000000000000000 : ℝ) ≤ (5004095388078073/5000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (12541509968166533351/12500000000000000000 : ℝ)^1024 ≤ (5004095388078073/5000000000000000 : ℝ)^4149 := by
      have hnat : (12541509968166533351 : ℕ)^1024*5000000000000000^4149 ≤ 5004095388078073^4149*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12541509968166533351 12500000000000000000 5004095388078073 5000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004095388078073/5000000000000000 : ℝ)) (X := (12541509968166533351/12500000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(756083136646027/100000000000000000000 : ℝ) ≤ ((3444003867021971441/3445000000000000000 : ℝ)+2*(254795472759/94737500000000 : ℝ)*(1089/20000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (3444003867021971441/3445000000000000000 : ℝ)+2*(254795472759/94737500000000 : ℝ)*(1089/20000 : ℝ)=(5000018660513929/5000000000000000 : ℝ) by norm_num, show 1+2*(756083136646027/100000000000000000000 : ℝ)=(50000756083136646027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(41509968166533351/25000000000000000000 : ℝ)+(756083136646027/100000000000000000000 : ℝ) ≤ ((3444003867021971441/3445000000000000000 : ℝ)+(254795472759/94737500000000 : ℝ)*((20603/100000 : ℝ)+(1089/20000 : ℝ)))^(4149/1024 : ℝ) := by
    rw [show (3444003867021971441/3445000000000000000 : ℝ)+(254795472759/94737500000000 : ℝ)*((20603/100000 : ℝ)+(1089/20000 : ℝ))=(5002057024296001/5000000000000000 : ℝ) by norm_num, show 1+(41509968166533351/25000000000000000000 : ℝ)+(756083136646027/100000000000000000000 : ℝ)=(100166795955802779431/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(41509968166533351/25000000000000000000 : ℝ) ≤ ((3444003867021971441/3445000000000000000 : ℝ)+2*(254795472759/94737500000000 : ℝ)*(20603/100000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (3444003867021971441/3445000000000000000 : ℝ)+2*(254795472759/94737500000000 : ℝ)*(20603/100000 : ℝ)=(5004095388078073/5000000000000000 : ℝ) by norm_num, show 1+2*(41509968166533351/25000000000000000000 : ℝ)=(12541509968166533351/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3444003867021971441/3445000000000000000 : ℝ)*(X 1 0+X 2 0)+(254795472759/94737500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (1089/20000 : ℝ)) (hi := (20603/100000 : ℝ)) (c := (3444003867021971441/3445000000000000000 : ℝ)) (alpha := (254795472759/94737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3444003867021971441/3445000000000000000 : ℝ)*(X 0 1+X 2 1)+(254795472759/94737500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (1089/20000 : ℝ)) (hi := (20603/100000 : ℝ)) (c := (3444003867021971441/3445000000000000000 : ℝ)) (alpha := (254795472759/94737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3444003867021971441/3445000000000000000 : ℝ)*(X 0 2+X 1 2)+(254795472759/94737500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (1089/20000 : ℝ)) (hi := (20603/100000 : ℝ)) (c := (3444003867021971441/3445000000000000000 : ℝ)) (alpha := (254795472759/94737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-541426657/2500000000 : ℝ)*X 0 0+(5517813739/10000000000 : ℝ)*X 0 1+(2576507859/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1075086163/2000000000 : ℝ)*X 1 0+(-2355638273/10000000000 : ℝ)*X 1 1+(5153016911/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5375430767/10000000000 : ℝ)*X 2 0+(1288254241/2500000000 : ℝ)*X 2 1+(-588909567/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358237129/10000000000 : ℝ)*X 0 0+(2006402057/5000000000 : ℝ)*X 0 1+(4733436667/10000000000 : ℝ)*X 0 2+(4358237129/10000000000 : ℝ)*X 1 0+(2006402057/5000000000 : ℝ)*X 1 1+(4733436667/10000000000 : ℝ)*X 1 2+(4358237129/10000000000 : ℝ)*X 2 0+(2006402057/5000000000 : ℝ)*X 2 1+(4733436667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2165819457/10000000000 : ℝ)*X 0 0+(5155596029/10000000000 : ℝ)*X 0 1+(5515207147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1320774127/2500000000 : ℝ)*X 1 0+(-1993447459/10000000000 : ℝ)*X 1 1+(5515207233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2641548327/5000000000 : ℝ)*X 2 0+(1378801793/2500000000 : ℝ)*X 2 1+(-1993447343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4358461339/10000000000 : ℝ)*X 0 0+(2364170219/5000000000 : ℝ)*X 0 1+(2008975657/5000000000 : ℝ)*X 0 2+(4358461339/10000000000 : ℝ)*X 1 0+(2364170219/5000000000 : ℝ)*X 1 1+(2008975657/5000000000 : ℝ)*X 1 2+(4358461339/10000000000 : ℝ)*X 2 0+(2364170219/5000000000 : ℝ)*X 2 1+(2008975657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (104663005437550487632514913/18218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (445494209/100000000000000 : ℝ)*(base19) + (237149363/100000000000000 : ℝ)*(base23) + (11464331/50000000000000 : ℝ)*(upper2) + (35832691/25000000000000 : ℝ)*(upper3) + (24352983/20000000000000 : ℝ)*(upper4) + (258058967230441/12500000000000 : ℝ)*(major0) + (258058967230441/12500000000000 : ℝ)*(major1) + (258058967230441/12500000000000 : ℝ)*(major2) + (42832115266533/1562500000000 : ℝ)*(sp0) + (274126596530397/10000000000000 : ℝ)*(sp1) + (171329135853051/6250000000000 : ℝ)*(sp2) + (138767262171789/10000000000000 : ℝ)*(sp3) + (11033740067/100000000000000 : ℝ)*(sp4) + (1062919443/25000000000000 : ℝ)*(sp7) + (1387676873395661/100000000000000 : ℝ)*(f.failure) + (1370633205399089/50000000000000 : ℝ)*(f.sum) + (10867239121913/2915000000000000000000000000 : ℝ)*base66 + (299207331104867093/36437500000000000000000000000000 : ℝ)*base68 + (26075110334117093/36437500000000000000000000000000 : ℝ)*base70 + (226539724646304593/36437500000000000000000000000000 : ℝ)*base72 + (4561094798479/1457500000000000000000000000 : ℝ)*base74 + (145275778778804593/36437500000000000000000000000000 : ℝ)*base76 + (190090795004179593/36437500000000000000000000000000 : ℝ)*base78 + (240474450434804593/36437500000000000000000000000000 : ℝ)*base80 + (1292991024491/1457500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (61401149/10000000000000000000000 : ℝ)*base90 + (61401149/10000000000000000000000 : ℝ)*base92 + (61401149/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64508870064161571862634577/7401367187500000000000000000000 : ℝ) := by norm_num
    linear_combination (1738943807/100000000000000 : ℝ)*(base19) + (495505073/25000000000000 : ℝ)*(base23) + (114371209/50000000000000 : ℝ)*(upper3) + (6041727/10000000000000 : ℝ)*(lower4) + (17142329/10000000000000 : ℝ)*(upper5) + (130889388125323/6250000000000 : ℝ)*(major0) + (130889388125323/6250000000000 : ℝ)*(major1) + (130889388125323/6250000000000 : ℝ)*(major2) + (7938541137/50000000000000 : ℝ)*(sp1) + (3768985261/20000000000000 : ℝ)*(sp2) + (695195122701111/25000000000000 : ℝ)*(sp4) + (1390381437389181/50000000000000 : ℝ)*(sp5) + (1390379831928923/50000000000000 : ℝ)*(sp6) + (703839819339531/50000000000000 : ℝ)*(sp7) + (703839819339531/50000000000000 : ℝ)*(f.failure) + (695195122701111/25000000000000 : ℝ)*(f.sum) + (80948430067677/18947500000000000000000000000 : ℝ)*base66 + (2462573378694795127/236843750000000000000000000000000 : ℝ)*base68 + (3028224157745295127/236843750000000000000000000000000 : ℝ)*base70 + (1943117053700045127/236843750000000000000000000000000 : ℝ)*base72 + (62061453127331/9473750000000000000000000000 : ℝ)*base74 + (3811340128328670127/236843750000000000000000000000000 : ℝ)*base76 + (1747209380529013877/236843750000000000000000000000000 : ℝ)*base78 + (1027432094189295127/236843750000000000000000000000000 : ℝ)*base80 + (44804698987077/18947500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (63970021/5000000000000000000000 : ℝ)*base89 + (63970021/5000000000000000000000 : ℝ)*base91 + (63970021/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1106_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20603/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1089/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1113/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16613/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1106_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1106_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1113/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16613/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1106_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1106_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1106_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1113/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16613/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1106_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
