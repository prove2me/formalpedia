-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1205_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:04:44.484901+00:00
-- url     : https://prove2.me/submissions/135586ce-802d-4c46-abd6-5a3dcc5a268e

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
theorem support_rectangle_w1205_s3_0 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-66685949/312500000 : ℝ)*x 0 + (1084599791/2000000000 : ℝ)*x 1 + (327353829/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66685949/312500000 : ℝ)^4199 ≤ (12966807113409/100000000000000 : ℝ)^3175 := by
    have hnat : (66685949 : ℕ)^4199*100000000000000^3175 ≤ 12966807113409^3175*312500000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66685949 312500000 12966807113409 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084599791/2000000000 : ℝ)^4199 ≤ (22258533064479/50000000000000 : ℝ)^3175 := by
    have hnat : (1084599791 : ℕ)^4199*50000000000000^3175 ≤ 22258533064479^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084599791 2000000000 22258533064479 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327353829/625000000 : ℝ)^4199 ≤ (42516126742771/100000000000000 : ℝ)^3175 := by
    have hnat : (327353829 : ℕ)^4199*100000000000000^3175 ≤ 42516126742771^3175*625000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327353829 625000000 42516126742771 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66685949/312500000 : ℝ), (1084599791/2000000000 : ℝ), (327353829/625000000 : ℝ)] ![(12966807113409/100000000000000 : ℝ), (22258533064479/50000000000000 : ℝ), (42516126742771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66685949/312500000 : ℝ)|^4199 ≤ (12966807113409/100000000000000 : ℝ)^3175
        have hw : |(-66685949/312500000 : ℝ)|=(66685949/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084599791/2000000000 : ℝ)|^4199 ≤ (22258533064479/50000000000000 : ℝ)^3175
        have hw : |(1084599791/2000000000 : ℝ)|=(1084599791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327353829/625000000 : ℝ)|^4199 ≤ (42516126742771/100000000000000 : ℝ)^3175
        have hw : |(327353829/625000000 : ℝ)|=(327353829/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s3_1 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070463747/2000000000 : ℝ)*x 0 + (-2228564769/10000000000 : ℝ)*x 1 + (2618830523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070463747/2000000000 : ℝ)^4199 ≤ (43751345058103/100000000000000 : ℝ)^3175 := by
    have hnat : (1070463747 : ℕ)^4199*100000000000000^3175 ≤ 43751345058103^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070463747 2000000000 43751345058103 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2228564769/10000000000 : ℝ)^4199 ≤ (13732530521/100000000000 : ℝ)^3175 := by
    have hnat : (2228564769 : ℕ)^4199*100000000000^3175 ≤ 13732530521^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228564769 10000000000 13732530521 100000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618830523/5000000000 : ℝ)^4199 ≤ (10629031100613/25000000000000 : ℝ)^3175 := by
    have hnat : (2618830523 : ℕ)^4199*25000000000000^3175 ≤ 10629031100613^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618830523 5000000000 10629031100613 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070463747/2000000000 : ℝ), (-2228564769/10000000000 : ℝ), (2618830523/5000000000 : ℝ)] ![(43751345058103/100000000000000 : ℝ), (13732530521/100000000000 : ℝ), (10629031100613/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070463747/2000000000 : ℝ)|^4199 ≤ (43751345058103/100000000000000 : ℝ)^3175
        have hw : |(1070463747/2000000000 : ℝ)|=(1070463747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2228564769/10000000000 : ℝ)|^4199 ≤ (13732530521/100000000000 : ℝ)^3175
        have hw : |(-2228564769/10000000000 : ℝ)|=(2228564769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618830523/5000000000 : ℝ)|^4199 ≤ (10629031100613/25000000000000 : ℝ)^3175
        have hw : |(2618830523/5000000000 : ℝ)|=(2618830523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s3_2 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133807971/250000000 : ℝ)*x 0 + (5237660939/10000000000 : ℝ)*x 1 + (-2228564771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133807971/250000000 : ℝ)^4199 ≤ (43751346193221/100000000000000 : ℝ)^3175 := by
    have hnat : (133807971 : ℕ)^4199*100000000000000^3175 ≤ 43751346193221^3175*250000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133807971 250000000 43751346193221 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237660939/10000000000 : ℝ)^4199 ≤ (10629030813441/25000000000000 : ℝ)^3175 := by
    have hnat : (5237660939 : ℕ)^4199*25000000000000^3175 ≤ 10629030813441^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237660939 10000000000 10629030813441 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2228564771/10000000000 : ℝ)^4199 ≤ (13732530537299/100000000000000 : ℝ)^3175 := by
    have hnat : (2228564771 : ℕ)^4199*100000000000000^3175 ≤ 13732530537299^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228564771 10000000000 13732530537299 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133807971/250000000 : ℝ), (5237660939/10000000000 : ℝ), (-2228564771/10000000000 : ℝ)] ![(43751346193221/100000000000000 : ℝ), (10629030813441/25000000000000 : ℝ), (13732530537299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133807971/250000000 : ℝ)|^4199 ≤ (43751346193221/100000000000000 : ℝ)^3175
        have hw : |(133807971/250000000 : ℝ)|=(133807971/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237660939/10000000000 : ℝ)|^4199 ≤ (10629030813441/25000000000000 : ℝ)^3175
        have hw : |(5237660939/10000000000 : ℝ)|=(5237660939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2228564771/10000000000 : ℝ)|^4199 ≤ (13732530537299/100000000000000 : ℝ)^3175
        have hw : |(-2228564771/10000000000 : ℝ)|=(2228564771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s3_3 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1088496417/2500000000 : ℝ)*x 0 + (417126043/1000000000 : ℝ)*x 1 + (2272273561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088496417/2500000000 : ℝ)^4199 ≤ (8324553547167/25000000000000 : ℝ)^3175 := by
    have hnat : (1088496417 : ℕ)^4199*25000000000000^3175 ≤ 8324553547167^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088496417 2500000000 8324553547167 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417126043/1000000000 : ℝ)^4199 ≤ (6292540685829/20000000000000 : ℝ)^3175 := by
    have hnat : (417126043 : ℕ)^4199*20000000000000^3175 ≤ 6292540685829^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417126043 1000000000 6292540685829 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2272273561/5000000000 : ℝ)^4199 ≤ (35239082358237/100000000000000 : ℝ)^3175 := by
    have hnat : (2272273561 : ℕ)^4199*100000000000000^3175 ≤ 35239082358237^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272273561 5000000000 35239082358237 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088496417/2500000000 : ℝ), (417126043/1000000000 : ℝ), (2272273561/5000000000 : ℝ)] ![(8324553547167/25000000000000 : ℝ), (6292540685829/20000000000000 : ℝ), (35239082358237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088496417/2500000000 : ℝ)|^4199 ≤ (8324553547167/25000000000000 : ℝ)^3175
        have hw : |(1088496417/2500000000 : ℝ)|=(1088496417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(417126043/1000000000 : ℝ)|^4199 ≤ (6292540685829/20000000000000 : ℝ)^3175
        have hw : |(417126043/1000000000 : ℝ)|=(417126043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2272273561/5000000000 : ℝ)|^4199 ≤ (35239082358237/100000000000000 : ℝ)^3175
        have hw : |(2272273561/5000000000 : ℝ)|=(2272273561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s3_4 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133965857/10000000000 : ℝ)*x 0 + (5238350769/10000000000 : ℝ)*x 1 + (1084461129/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133965857/10000000000 : ℝ)^4199 ≤ (6483465793149/50000000000000 : ℝ)^3175 := by
    have hnat : (2133965857 : ℕ)^4199*50000000000000^3175 ≤ 6483465793149^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133965857 10000000000 6483465793149 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238350769/10000000000 : ℝ)^4199 ≤ (531544112691/1250000000000 : ℝ)^3175 := by
    have hnat : (5238350769 : ℕ)^4199*1250000000000^3175 ≤ 531544112691^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238350769 10000000000 531544112691 1250000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084461129/2000000000 : ℝ)^4199 ≤ (173865388187/390625000000 : ℝ)^3175 := by
    have hnat : (1084461129 : ℕ)^4199*390625000000^3175 ≤ 173865388187^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084461129 2000000000 173865388187 390625000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133965857/10000000000 : ℝ), (5238350769/10000000000 : ℝ), (1084461129/2000000000 : ℝ)] ![(6483465793149/50000000000000 : ℝ), (531544112691/1250000000000 : ℝ), (173865388187/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133965857/10000000000 : ℝ)|^4199 ≤ (6483465793149/50000000000000 : ℝ)^3175
        have hw : |(-2133965857/10000000000 : ℝ)|=(2133965857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238350769/10000000000 : ℝ)|^4199 ≤ (531544112691/1250000000000 : ℝ)^3175
        have hw : |(5238350769/10000000000 : ℝ)|=(5238350769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084461129/2000000000 : ℝ)|^4199 ≤ (173865388187/390625000000 : ℝ)^3175
        have hw : |(1084461129/2000000000 : ℝ)|=(1084461129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s3_5 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652576489/5000000000 : ℝ)*x 0 + (-1021960181/5000000000 : ℝ)*x 1 + (5422306011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652576489/5000000000 : ℝ)^4199 ≤ (8648435771839/20000000000000 : ℝ)^3175 := by
    have hnat : (2652576489 : ℕ)^4199*20000000000000^3175 ≤ 8648435771839^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652576489 5000000000 8648435771839 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021960181/5000000000 : ℝ)^4199 ≤ (1531034722009/12500000000000 : ℝ)^3175 := by
    have hnat : (1021960181 : ℕ)^4199*12500000000000^3175 ≤ 1531034722009^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021960181 5000000000 1531034722009 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422306011/10000000000 : ℝ)^4199 ≤ (44509543349181/100000000000000 : ℝ)^3175 := by
    have hnat : (5422306011 : ℕ)^4199*100000000000000^3175 ≤ 44509543349181^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422306011 10000000000 44509543349181 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652576489/5000000000 : ℝ), (-1021960181/5000000000 : ℝ), (5422306011/10000000000 : ℝ)] ![(8648435771839/20000000000000 : ℝ), (1531034722009/12500000000000 : ℝ), (44509543349181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652576489/5000000000 : ℝ)|^4199 ≤ (8648435771839/20000000000000 : ℝ)^3175
        have hw : |(2652576489/5000000000 : ℝ)|=(2652576489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021960181/5000000000 : ℝ)|^4199 ≤ (1531034722009/12500000000000 : ℝ)^3175
        have hw : |(-1021960181/5000000000 : ℝ)|=(1021960181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422306011/10000000000 : ℝ)|^4199 ≤ (44509543349181/100000000000000 : ℝ)^3175
        have hw : |(5422306011/10000000000 : ℝ)|=(5422306011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s3_6 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652577151/5000000000 : ℝ)*x 0 + (1355576353/2500000000 : ℝ)*x 1 + (-1021959691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652577151/5000000000 : ℝ)^4199 ≤ (21621096565843/50000000000000 : ℝ)^3175 := by
    have hnat : (2652577151 : ℕ)^4199*50000000000000^3175 ≤ 21621096565843^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652577151 5000000000 21621096565843 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355576353/2500000000 : ℝ)^4199 ≤ (2781846052901/6250000000000 : ℝ)^3175 := by
    have hnat : (1355576353 : ℕ)^4199*6250000000000^3175 ≤ 2781846052901^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355576353 2500000000 2781846052901 6250000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021959691/5000000000 : ℝ)^4199 ≤ (12248270009323/100000000000000 : ℝ)^3175 := by
    have hnat : (1021959691 : ℕ)^4199*100000000000000^3175 ≤ 12248270009323^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021959691 5000000000 12248270009323 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652577151/5000000000 : ℝ), (1355576353/2500000000 : ℝ), (-1021959691/5000000000 : ℝ)] ![(21621096565843/50000000000000 : ℝ), (2781846052901/6250000000000 : ℝ), (12248270009323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652577151/5000000000 : ℝ)|^4199 ≤ (21621096565843/50000000000000 : ℝ)^3175
        have hw : |(2652577151/5000000000 : ℝ)|=(2652577151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355576353/2500000000 : ℝ)|^4199 ≤ (2781846052901/6250000000000 : ℝ)^3175
        have hw : |(1355576353/2500000000 : ℝ)|=(1355576353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1021959691/5000000000 : ℝ)|^4199 ≤ (12248270009323/100000000000000 : ℝ)^3175
        have hw : |(-1021959691/5000000000 : ℝ)|=(1021959691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s3_7 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4354016601/10000000000 : ℝ)*x 0 + (4543159051/10000000000 : ℝ)*x 1 + (2086327949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354016601/10000000000 : ℝ)^4199 ≤ (4162315881857/12500000000000 : ℝ)^3175 := by
    have hnat : (4354016601 : ℕ)^4199*12500000000000^3175 ≤ 4162315881857^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354016601 10000000000 4162315881857 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4543159051/10000000000 : ℝ)^4199 ≤ (35224848376227/100000000000000 : ℝ)^3175 := by
    have hnat : (4543159051 : ℕ)^4199*100000000000000^3175 ≤ 35224848376227^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543159051 10000000000 35224848376227 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086327949/5000000000 : ℝ)^4199 ≤ (31476624549401/100000000000000 : ℝ)^3175 := by
    have hnat : (2086327949 : ℕ)^4199*100000000000000^3175 ≤ 31476624549401^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086327949 5000000000 31476624549401 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354016601/10000000000 : ℝ), (4543159051/10000000000 : ℝ), (2086327949/5000000000 : ℝ)] ![(4162315881857/12500000000000 : ℝ), (35224848376227/100000000000000 : ℝ), (31476624549401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354016601/10000000000 : ℝ)|^4199 ≤ (4162315881857/12500000000000 : ℝ)^3175
        have hw : |(4354016601/10000000000 : ℝ)|=(4354016601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4543159051/10000000000 : ℝ)|^4199 ≤ (35224848376227/100000000000000 : ℝ)^3175
        have hw : |(4543159051/10000000000 : ℝ)|=(4543159051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086327949/5000000000 : ℝ)|^4199 ≤ (31476624549401/100000000000000 : ℝ)^3175
        have hw : |(2086327949/5000000000 : ℝ)|=(2086327949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1205_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5407/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (921/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8161/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4673/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8161/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4673/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8161/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4673/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8161/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4673/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8161/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4673/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8161/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4673/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4673/50000 : ℝ) ^ (8397/2048 : ℝ) ≤ (6018179813214403/100000000000000000000 : ℝ) := by
    have hpowers : (4673/50000 : ℝ)^8397 ≤ (6018179813214403/100000000000000000000 : ℝ)^2048 := by
      have hnat : (4673 : ℕ)^8397*100000000000000000000^2048 ≤ 6018179813214403^2048*50000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4673 50000 6018179813214403 100000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4673/50000 : ℝ)) (X := (6018179813214403/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8161/50000 : ℝ) ^ (8397/2048 : ℝ) ≤ (59196217039930757/100000000000000000000 : ℝ) := by
    have hpowers : (8161/50000 : ℝ)^8397 ≤ (59196217039930757/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8161 : ℕ)^8397*100000000000000000000^2048 ≤ 59196217039930757^2048*50000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8161 50000 59196217039930757 100000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8161/50000 : ℝ)) (X := (59196217039930757/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006018179813214403/50000000000000000000 : ℝ) ≤ (2000058709879499/2000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (50006018179813214403/50000000000000000000 : ℝ)^2048 ≤ (2000058709879499/2000000000000000 : ℝ)^8397 := by
      have hnat : (50006018179813214403 : ℕ)^2048*2000000000000000^8397 ≤ 2000058709879499^8397*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006018179813214403 50000000000000000000 2000058709879499 2000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000058709879499/2000000000000000 : ℝ)) (X := (50006018179813214403/50000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501630359921328629/2500000000000000000 : ℝ) ≤ (1250198770645933/1250000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (2501630359921328629/2500000000000000000 : ℝ)^2048 ≤ (1250198770645933/1250000000000000 : ℝ)^8397 := by
      have hnat : (2501630359921328629 : ℕ)^2048*1250000000000000^8397 ≤ 1250198770645933^8397*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501630359921328629 2500000000000000000 1250198770645933 1250000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250198770645933/1250000000000000 : ℝ)) (X := (2501630359921328629/2500000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50059196217039930757/50000000000000000000 : ℝ) ≤ (10002886780937433/10000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (50059196217039930757/50000000000000000000 : ℝ)^2048 ≤ (10002886780937433/10000000000000000 : ℝ)^8397 := by
      have hnat : (50059196217039930757 : ℕ)^2048*10000000000000000^8397 ≤ 10002886780937433^8397*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50059196217039930757 50000000000000000000 10002886780937433 10000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002886780937433/10000000000000000 : ℝ)) (X := (50059196217039930757/50000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6018179813214403/100000000000000000000 : ℝ) ≤ ((17434452864656166143/17440000000000000000 : ℝ)+2*(1296615769969/697600000000000 : ℝ)*(4673/50000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (17434452864656166143/17440000000000000000 : ℝ)+2*(1296615769969/697600000000000 : ℝ)*(4673/50000 : ℝ)=(2000058709879499/2000000000000000 : ℝ) by norm_num, show 1+2*(6018179813214403/100000000000000000000 : ℝ)=(50006018179813214403/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(59196217039930757/100000000000000000000 : ℝ)+(6018179813214403/100000000000000000000 : ℝ) ≤ ((17434452864656166143/17440000000000000000 : ℝ)+(1296615769969/697600000000000 : ℝ)*((8161/50000 : ℝ)+(4673/50000 : ℝ)))^(8397/2048 : ℝ) := by
    rw [show (17434452864656166143/17440000000000000000 : ℝ)+(1296615769969/697600000000000 : ℝ)*((8161/50000 : ℝ)+(4673/50000 : ℝ))=(1250198770645933/1250000000000000 : ℝ) by norm_num, show 1+(59196217039930757/100000000000000000000 : ℝ)+(6018179813214403/100000000000000000000 : ℝ)=(2501630359921328629/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(59196217039930757/100000000000000000000 : ℝ) ≤ ((17434452864656166143/17440000000000000000 : ℝ)+2*(1296615769969/697600000000000 : ℝ)*(8161/50000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (17434452864656166143/17440000000000000000 : ℝ)+2*(1296615769969/697600000000000 : ℝ)*(8161/50000 : ℝ)=(10002886780937433/10000000000000000 : ℝ) by norm_num, show 1+2*(59196217039930757/100000000000000000000 : ℝ)=(50059196217039930757/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17434452864656166143/17440000000000000000 : ℝ)*(X 1 0+X 2 0)+(1296615769969/697600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (4673/50000 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (17434452864656166143/17440000000000000000 : ℝ)) (alpha := (1296615769969/697600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17434452864656166143/17440000000000000000 : ℝ)*(X 0 1+X 2 1)+(1296615769969/697600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (4673/50000 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (17434452864656166143/17440000000000000000 : ℝ)) (alpha := (1296615769969/697600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17434452864656166143/17440000000000000000 : ℝ)*(X 0 2+X 1 2)+(1296615769969/697600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (4673/50000 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (17434452864656166143/17440000000000000000 : ℝ)) (alpha := (1296615769969/697600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66685949/312500000 : ℝ)*X 0 0+(1084599791/2000000000 : ℝ)*X 0 1+(327353829/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070463747/2000000000 : ℝ)*X 1 0+(-2228564769/10000000000 : ℝ)*X 1 1+(2618830523/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133807971/250000000 : ℝ)*X 2 0+(5237660939/10000000000 : ℝ)*X 2 1+(-2228564771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088496417/2500000000 : ℝ)*X 0 0+(417126043/1000000000 : ℝ)*X 0 1+(2272273561/5000000000 : ℝ)*X 0 2+(1088496417/2500000000 : ℝ)*X 1 0+(417126043/1000000000 : ℝ)*X 1 1+(2272273561/5000000000 : ℝ)*X 1 2+(1088496417/2500000000 : ℝ)*X 2 0+(417126043/1000000000 : ℝ)*X 2 1+(2272273561/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2133965857/10000000000 : ℝ)*X 0 0+(5238350769/10000000000 : ℝ)*X 0 1+(1084461129/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652576489/5000000000 : ℝ)*X 1 0+(-1021960181/5000000000 : ℝ)*X 1 1+(5422306011/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652577151/5000000000 : ℝ)*X 2 0+(1355576353/2500000000 : ℝ)*X 2 1+(-1021959691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354016601/10000000000 : ℝ)*X 0 0+(4543159051/10000000000 : ℝ)*X 0 1+(2086327949/5000000000 : ℝ)*X 0 2+(4354016601/10000000000 : ℝ)*X 1 0+(4543159051/10000000000 : ℝ)*X 1 1+(2086327949/5000000000 : ℝ)*X 1 2+(4354016601/10000000000 : ℝ)*X 2 0+(4543159051/10000000000 : ℝ)*X 2 1+(2086327949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15270866151683018331541641/5450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (807530881/100000000000000 : ℝ)*(base19) + (219925053/25000000000000 : ℝ)*(base23) + (18026209/100000000000000 : ℝ)*(lower2) + (84000567/100000000000000 : ℝ)*(upper3) + (3040983/4000000000000 : ℝ)*(upper5) + (25232791763171/625000000000 : ℝ)*(major0) + (25232791763171/625000000000 : ℝ)*(major1) + (25232791763171/625000000000 : ℝ)*(major2) + (6744456992231/125000000000 : ℝ)*(sp0) + (1079114938892069/20000000000000 : ℝ)*(sp1) + (2697787311145507/50000000000000 : ℝ)*(sp2) + (334863951082531/12500000000000 : ℝ)*(sp3) + (4954103213/50000000000000 : ℝ)*(sp4) + (6160163447/100000000000000 : ℝ)*(sp7) + (535783553764739/20000000000000 : ℝ)*(f.failure) + (2697787750995613/50000000000000 : ℝ)*(f.sum) + (940722540977/218000000000000000000000000 : ℝ)*base65 + (100814977139094453/10900000000000000000000000000000 : ℝ)*base67 + (20980024288194453/10900000000000000000000000000000 : ℝ)*base69 + (5484568080405547/10900000000000000000000000000000 : ℝ)*base72 + (240685797077/218000000000000000000000000 : ℝ)*base74 + (27943392278194453/10900000000000000000000000000000 : ℝ)*base75 + (180503873903094453/10900000000000000000000000000000 : ℝ)*base77 + (82040987277705547/10900000000000000000000000000000 : ℝ)*base80 + (23956909661/8720000000000000000000000 : ℝ)*base82 + (549579/200000000000000000000 : ℝ)*base90 + (549579/200000000000000000000 : ℝ)*base92 + (549579/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (479348350140931527378171969/218000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216877773/50000000000000 : ℝ)*(base19) + (2288979409/100000000000000 : ℝ)*(base23) + (7166503/12500000000000 : ℝ)*(upper2) + (233928291/100000000000000 : ℝ)*(upper3) + (1016895784936087/25000000000000 : ℝ)*(major0) + (1016895784936087/25000000000000 : ℝ)*(major1) + (1016895784936087/25000000000000 : ℝ)*(major2) + (138436001/1562500000000 : ℝ)*(sp1) + (16494067/31250000000 : ℝ)*(sp2) + (1530712753/50000000000000 : ℝ)*(sp3) + (271805933018481/5000000000000 : ℝ)*(sp4) + (543610936671001/10000000000000 : ℝ)*(sp5) + (1359015897593953/25000000000000 : ℝ)*(sp6) + (539808896879741/20000000000000 : ℝ)*(sp7) + (674761886456053/25000000000000 : ℝ)*(f.failure) + (271805933018481/5000000000000 : ℝ)*(f.sum) + (34406793481257/8720000000000000000000000000 : ℝ)*base66 + (4464135109349122559/436000000000000000000000000000000 : ℝ)*base68 + (2777607062801122559/436000000000000000000000000000000 : ℝ)*base70 + (4210428548397122559/436000000000000000000000000000000 : ℝ)*base72 + (21584968956023/8720000000000000000000000000 : ℝ)*base73 + (2565822745945122559/436000000000000000000000000000000 : ℝ)*base76 + (2726323964541122559/436000000000000000000000000000000 : ℝ)*base78 + (5094930476053122559/436000000000000000000000000000000 : ℝ)*base80 + (36656586095943/8720000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2917267/250000000000000000000 : ℝ)*base89 + (2917267/250000000000000000000 : ℝ)*base91 + (2917267/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1205_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (921/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1205_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1205_s4_0 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1068241903/5000000000 : ℝ)*x 0 + (5399030087/10000000000 : ℝ)*x 1 + (32874819/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068241903/5000000000 : ℝ)^4199 ≤ (6493585115673/50000000000000 : ℝ)^3175 := by
    have hnat : (1068241903 : ℕ)^4199*50000000000000^3175 ≤ 6493585115673^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068241903 5000000000 6493585115673 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399030087/10000000000 : ℝ)^4199 ≤ (5532129271737/12500000000000 : ℝ)^3175 := by
    have hnat : (5399030087 : ℕ)^4199*12500000000000^3175 ≤ 5532129271737^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399030087 10000000000 5532129271737 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32874819/62500000 : ℝ)^4199 ≤ (42755795576073/100000000000000 : ℝ)^3175 := by
    have hnat : (32874819 : ℕ)^4199*100000000000000^3175 ≤ 42755795576073^3175*62500000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32874819 62500000 42755795576073 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1068241903/5000000000 : ℝ), (5399030087/10000000000 : ℝ), (32874819/62500000 : ℝ)] ![(6493585115673/50000000000000 : ℝ), (5532129271737/12500000000000 : ℝ), (42755795576073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1068241903/5000000000 : ℝ)|^4199 ≤ (6493585115673/50000000000000 : ℝ)^3175
        have hw : |(-1068241903/5000000000 : ℝ)|=(1068241903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399030087/10000000000 : ℝ)|^4199 ≤ (5532129271737/12500000000000 : ℝ)^3175
        have hw : |(5399030087/10000000000 : ℝ)|=(5399030087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32874819/62500000 : ℝ)|^4199 ≤ (42755795576073/100000000000000 : ℝ)^3175
        have hw : |(32874819/62500000 : ℝ)|=(32874819/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s4_1 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673148367/5000000000 : ℝ)*x 0 + (-441421743/2000000000 : ℝ)*x 1 + (2629985583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673148367/5000000000 : ℝ)^4199 ≤ (10921563790241/25000000000000 : ℝ)^3175 := by
    have hnat : (2673148367 : ℕ)^4199*25000000000000^3175 ≤ 10921563790241^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673148367 5000000000 10921563790241 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441421743/2000000000 : ℝ)^4199 ≤ (13557947887361/100000000000000 : ℝ)^3175 := by
    have hnat : (441421743 : ℕ)^4199*100000000000000^3175 ≤ 13557947887361^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441421743 2000000000 13557947887361 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629985583/5000000000 : ℝ)^4199 ≤ (42755796930589/100000000000000 : ℝ)^3175 := by
    have hnat : (2629985583 : ℕ)^4199*100000000000000^3175 ≤ 42755796930589^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629985583 5000000000 42755796930589 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673148367/5000000000 : ℝ), (-441421743/2000000000 : ℝ), (2629985583/5000000000 : ℝ)] ![(10921563790241/25000000000000 : ℝ), (13557947887361/100000000000000 : ℝ), (42755796930589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673148367/5000000000 : ℝ)|^4199 ≤ (10921563790241/25000000000000 : ℝ)^3175
        have hw : |(2673148367/5000000000 : ℝ)|=(2673148367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441421743/2000000000 : ℝ)|^4199 ≤ (13557947887361/100000000000000 : ℝ)^3175
        have hw : |(-441421743/2000000000 : ℝ)|=(441421743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629985583/5000000000 : ℝ)|^4199 ≤ (42755796930589/100000000000000 : ℝ)^3175
        have hw : |(2629985583/5000000000 : ℝ)|=(2629985583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s4_2 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673148359/5000000000 : ℝ)*x 0 + (2629985533/5000000000 : ℝ)*x 1 + (-220710887/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673148359/5000000000 : ℝ)^4199 ≤ (43686254988057/100000000000000 : ℝ)^3175 := by
    have hnat : (2673148359 : ℕ)^4199*100000000000000^3175 ≤ 43686254988057^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673148359 5000000000 43686254988057 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629985533/5000000000 : ℝ)^4199 ≤ (5344474481947/12500000000000 : ℝ)^3175 := by
    have hnat : (2629985533 : ℕ)^4199*12500000000000^3175 ≤ 5344474481947^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629985533 5000000000 5344474481947 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220710887/1000000000 : ℝ)^4199 ≤ (3389487286647/25000000000000 : ℝ)^3175 := by
    have hnat : (220710887 : ℕ)^4199*25000000000000^3175 ≤ 3389487286647^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220710887 1000000000 3389487286647 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673148359/5000000000 : ℝ), (2629985533/5000000000 : ℝ), (-220710887/1000000000 : ℝ)] ![(43686254988057/100000000000000 : ℝ), (5344474481947/12500000000000 : ℝ), (3389487286647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673148359/5000000000 : ℝ)|^4199 ≤ (43686254988057/100000000000000 : ℝ)^3175
        have hw : |(2673148359/5000000000 : ℝ)|=(2673148359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629985533/5000000000 : ℝ)|^4199 ≤ (5344474481947/12500000000000 : ℝ)^3175
        have hw : |(2629985533/5000000000 : ℝ)|=(2629985533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220710887/1000000000 : ℝ)|^4199 ≤ (3389487286647/25000000000000 : ℝ)^3175
        have hw : |(-220710887/1000000000 : ℝ)|=(220710887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s4_3 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2177751061/5000000000 : ℝ)*x 0 + (4217670691/10000000000 : ℝ)*x 1 + (4497747789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177751061/5000000000 : ℝ)^4199 ≤ (33313552929979/100000000000000 : ℝ)^3175 := by
    have hnat : (2177751061 : ℕ)^4199*100000000000000^3175 ≤ 33313552929979^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177751061 5000000000 33313552929979 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4217670691/10000000000 : ℝ)^4199 ≤ (798162337807/2500000000000 : ℝ)^3175 := by
    have hnat : (4217670691 : ℕ)^4199*2500000000000^3175 ≤ 798162337807^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217670691 10000000000 798162337807 2500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497747789/10000000000 : ℝ)^4199 ≤ (17379976769067/50000000000000 : ℝ)^3175 := by
    have hnat : (4497747789 : ℕ)^4199*50000000000000^3175 ≤ 17379976769067^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497747789 10000000000 17379976769067 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177751061/5000000000 : ℝ), (4217670691/10000000000 : ℝ), (4497747789/10000000000 : ℝ)] ![(33313552929979/100000000000000 : ℝ), (798162337807/2500000000000 : ℝ), (17379976769067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177751061/5000000000 : ℝ)|^4199 ≤ (33313552929979/100000000000000 : ℝ)^3175
        have hw : |(2177751061/5000000000 : ℝ)|=(2177751061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4217670691/10000000000 : ℝ)|^4199 ≤ (798162337807/2500000000000 : ℝ)^3175
        have hw : |(4217670691/10000000000 : ℝ)|=(4217670691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497747789/10000000000 : ℝ)|^4199 ≤ (17379976769067/50000000000000 : ℝ)^3175
        have hw : |(4497747789/10000000000 : ℝ)|=(4497747789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s4_4 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-42729791/200000000 : ℝ)*x 0 + (5260359747/10000000000 : ℝ)*x 1 + (5398640369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42729791/200000000 : ℝ)^4199 ≤ (6493608204491/50000000000000 : ℝ)^3175 := by
    have hnat : (42729791 : ℕ)^4199*50000000000000^3175 ≤ 6493608204491^3175*200000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42729791 200000000 6493608204491 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260359747/10000000000 : ℝ)^4199 ≤ (42759974277303/100000000000000 : ℝ)^3175 := by
    have hnat : (5260359747 : ℕ)^4199*100000000000000^3175 ≤ 42759974277303^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260359747 10000000000 42759974277303 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398640369/10000000000 : ℝ)^4199 ≤ (22126404648233/50000000000000 : ℝ)^3175 := by
    have hnat : (5398640369 : ℕ)^4199*50000000000000^3175 ≤ 22126404648233^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398640369 10000000000 22126404648233 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42729791/200000000 : ℝ), (5260359747/10000000000 : ℝ), (5398640369/10000000000 : ℝ)] ![(6493608204491/50000000000000 : ℝ), (42759974277303/100000000000000 : ℝ), (22126404648233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42729791/200000000 : ℝ)|^4199 ≤ (6493608204491/50000000000000 : ℝ)^3175
        have hw : |(-42729791/200000000 : ℝ)|=(42729791/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260359747/10000000000 : ℝ)|^4199 ≤ (42759974277303/100000000000000 : ℝ)^3175
        have hw : |(5260359747/10000000000 : ℝ)|=(5260359747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398640369/10000000000 : ℝ)|^4199 ≤ (22126404648233/50000000000000 : ℝ)^3175
        have hw : |(5398640369/10000000000 : ℝ)|=(5398640369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s4_5 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1327726719/2500000000 : ℝ)*x 0 + (-2068440433/10000000000 : ℝ)*x 1 + (2699319929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327726719/2500000000 : ℝ)^4199 ≤ (86608431463/200000000000 : ℝ)^3175 := by
    have hnat : (1327726719 : ℕ)^4199*200000000000^3175 ≤ 86608431463^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327726719 2500000000 86608431463 200000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068440433/10000000000 : ℝ)^4199 ≤ (12442980499083/100000000000000 : ℝ)^3175 := by
    have hnat : (2068440433 : ℕ)^4199*100000000000000^3175 ≤ 12442980499083^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068440433 10000000000 12442980499083 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699319929/5000000000 : ℝ)^4199 ≤ (11063200939213/25000000000000 : ℝ)^3175 := by
    have hnat : (2699319929 : ℕ)^4199*25000000000000^3175 ≤ 11063200939213^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699319929 5000000000 11063200939213 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327726719/2500000000 : ℝ), (-2068440433/10000000000 : ℝ), (2699319929/5000000000 : ℝ)] ![(86608431463/200000000000 : ℝ), (12442980499083/100000000000000 : ℝ), (11063200939213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327726719/2500000000 : ℝ)|^4199 ≤ (86608431463/200000000000 : ℝ)^3175
        have hw : |(1327726719/2500000000 : ℝ)|=(1327726719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2068440433/10000000000 : ℝ)|^4199 ≤ (12442980499083/100000000000000 : ℝ)^3175
        have hw : |(-2068440433/10000000000 : ℝ)|=(2068440433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699319929/5000000000 : ℝ)|^4199 ≤ (11063200939213/25000000000000 : ℝ)^3175
        have hw : |(2699319929/5000000000 : ℝ)|=(2699319929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s4_6 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310907599/10000000000 : ℝ)*x 0 + (1079727873/2000000000 : ℝ)*x 1 + (-517110031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310907599/10000000000 : ℝ)^4199 ≤ (43304223528041/100000000000000 : ℝ)^3175 := by
    have hnat : (5310907599 : ℕ)^4199*100000000000000^3175 ≤ 43304223528041^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310907599 10000000000 43304223528041 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079727873/2000000000 : ℝ)^4199 ≤ (11063199603093/25000000000000 : ℝ)^3175 := by
    have hnat : (1079727873 : ℕ)^4199*25000000000000^3175 ≤ 11063199603093^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079727873 2000000000 11063199603093 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517110031/2500000000 : ℝ)^4199 ≤ (12442978040743/100000000000000 : ℝ)^3175 := by
    have hnat : (517110031 : ℕ)^4199*100000000000000^3175 ≤ 12442978040743^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517110031 2500000000 12442978040743 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310907599/10000000000 : ℝ), (1079727873/2000000000 : ℝ), (-517110031/2500000000 : ℝ)] ![(43304223528041/100000000000000 : ℝ), (11063199603093/25000000000000 : ℝ), (12442978040743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310907599/10000000000 : ℝ)|^4199 ≤ (43304223528041/100000000000000 : ℝ)^3175
        have hw : |(5310907599/10000000000 : ℝ)|=(5310907599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079727873/2000000000 : ℝ)|^4199 ≤ (11063199603093/25000000000000 : ℝ)^3175
        have hw : |(1079727873/2000000000 : ℝ)|=(1079727873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-517110031/2500000000 : ℝ)|^4199 ≤ (12442978040743/100000000000000 : ℝ)^3175
        have hw : |(-517110031/2500000000 : ℝ)|=(517110031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s4_7 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4355515603/10000000000 : ℝ)*x 0 + (4496964541/10000000000 : ℝ)*x 1 + (4218456683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355515603/10000000000 : ℝ)^4199 ≤ (16656844648161/50000000000000 : ℝ)^3175 := by
    have hnat : (4355515603 : ℕ)^4199*50000000000000^3175 ≤ 16656844648161^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355515603 10000000000 16656844648161 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496964541/10000000000 : ℝ)^4199 ≤ (34751948317031/100000000000000 : ℝ)^3175 := by
    have hnat : (4496964541 : ℕ)^4199*100000000000000^3175 ≤ 34751948317031^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496964541 10000000000 34751948317031 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4218456683/10000000000 : ℝ)^4199 ≤ (7983590593331/25000000000000 : ℝ)^3175 := by
    have hnat : (4218456683 : ℕ)^4199*25000000000000^3175 ≤ 7983590593331^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218456683 10000000000 7983590593331 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355515603/10000000000 : ℝ), (4496964541/10000000000 : ℝ), (4218456683/10000000000 : ℝ)] ![(16656844648161/50000000000000 : ℝ), (34751948317031/100000000000000 : ℝ), (7983590593331/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355515603/10000000000 : ℝ)|^4199 ≤ (16656844648161/50000000000000 : ℝ)^3175
        have hw : |(4355515603/10000000000 : ℝ)|=(4355515603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496964541/10000000000 : ℝ)|^4199 ≤ (34751948317031/100000000000000 : ℝ)^3175
        have hw : |(4496964541/10000000000 : ℝ)|=(4496964541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4218456683/10000000000 : ℝ)|^4199 ≤ (7983590593331/25000000000000 : ℝ)^3175
        have hw : |(4218456683/10000000000 : ℝ)|=(4218456683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1205_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1129/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (921/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5407/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (921/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5407/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (921/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5407/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (921/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5407/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (921/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5407/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (921/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5407/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5407/50000 : ℝ) ^ (8397/2048 : ℝ) ≤ (1368232093888531/12500000000000000000 : ℝ) := by
    have hpowers : (5407/50000 : ℝ)^8397 ≤ (1368232093888531/12500000000000000000 : ℝ)^2048 := by
      have hnat : (5407 : ℕ)^8397*12500000000000000000^2048 ≤ 1368232093888531^2048*50000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5407 50000 1368232093888531 12500000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5407/50000 : ℝ)) (X := (1368232093888531/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (921/6250 : ℝ) ^ (8397/2048 : ℝ) ≤ (38929174969979369/100000000000000000000 : ℝ) := by
    have hpowers : (921/6250 : ℝ)^8397 ≤ (38929174969979369/100000000000000000000 : ℝ)^2048 := by
      have hnat : (921 : ℕ)^8397*100000000000000000000^2048 ≤ 38929174969979369^2048*6250^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        921 6250 38929174969979369 100000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (921/6250 : ℝ)) (X := (38929174969979369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251368232093888531/6250000000000000000 : ℝ) ≤ (78129170994771/78125000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (6251368232093888531/6250000000000000000 : ℝ)^2048 ≤ (78129170994771/78125000000000 : ℝ)^8397 := by
      have hnat : (6251368232093888531 : ℕ)^2048*78125000000000^8397 ≤ 78129170994771^8397*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251368232093888531 6250000000000000000 78129170994771 78125000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78129170994771/78125000000000 : ℝ)) (X := (6251368232093888531/6250000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049875031721087617/100000000000000000000 : ℝ) ≤ (5000608102959243/5000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (100049875031721087617/100000000000000000000 : ℝ)^2048 ≤ (5000608102959243/5000000000000000 : ℝ)^8397 := by
      have hnat : (100049875031721087617 : ℕ)^2048*5000000000000000^8397 ≤ 5000608102959243^8397*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049875031721087617 100000000000000000000 5000608102959243 5000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000608102959243/5000000000000000 : ℝ)) (X := (100049875031721087617/100000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038929174969979369/50000000000000000000 : ℝ) ≤ (2500474631126571/2500000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (50038929174969979369/50000000000000000000 : ℝ)^2048 ≤ (2500474631126571/2500000000000000 : ℝ)^8397 := by
      have hnat : (50038929174969979369 : ℕ)^2048*2500000000000000^8397 ≤ 2500474631126571^8397*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038929174969979369 50000000000000000000 2500474631126571 2500000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500474631126571/2500000000000000 : ℝ)) (X := (50038929174969979369/50000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1368232093888531/12500000000000000000 : ℝ) ≤ ((4900917089961757899/4902500000000000000 : ℝ)+2*(341159293899/196100000000000 : ℝ)*(5407/50000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (4900917089961757899/4902500000000000000 : ℝ)+2*(341159293899/196100000000000 : ℝ)*(5407/50000 : ℝ)=(78129170994771/78125000000000 : ℝ) by norm_num, show 1+2*(1368232093888531/12500000000000000000 : ℝ)=(6251368232093888531/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38929174969979369/100000000000000000000 : ℝ)+(1368232093888531/12500000000000000000 : ℝ) ≤ ((4900917089961757899/4902500000000000000 : ℝ)+(341159293899/196100000000000 : ℝ)*((921/6250 : ℝ)+(5407/50000 : ℝ)))^(8397/2048 : ℝ) := by
    rw [show (4900917089961757899/4902500000000000000 : ℝ)+(341159293899/196100000000000 : ℝ)*((921/6250 : ℝ)+(5407/50000 : ℝ))=(5000608102959243/5000000000000000 : ℝ) by norm_num, show 1+(38929174969979369/100000000000000000000 : ℝ)+(1368232093888531/12500000000000000000 : ℝ)=(100049875031721087617/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38929174969979369/100000000000000000000 : ℝ) ≤ ((4900917089961757899/4902500000000000000 : ℝ)+2*(341159293899/196100000000000 : ℝ)*(921/6250 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (4900917089961757899/4902500000000000000 : ℝ)+2*(341159293899/196100000000000 : ℝ)*(921/6250 : ℝ)=(2500474631126571/2500000000000000 : ℝ) by norm_num, show 1+2*(38929174969979369/100000000000000000000 : ℝ)=(50038929174969979369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4900917089961757899/4902500000000000000 : ℝ)*(X 1 0+X 2 0)+(341159293899/196100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (5407/50000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (4900917089961757899/4902500000000000000 : ℝ)) (alpha := (341159293899/196100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4900917089961757899/4902500000000000000 : ℝ)*(X 0 1+X 2 1)+(341159293899/196100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (5407/50000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (4900917089961757899/4902500000000000000 : ℝ)) (alpha := (341159293899/196100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4900917089961757899/4902500000000000000 : ℝ)*(X 0 2+X 1 2)+(341159293899/196100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (5407/50000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (4900917089961757899/4902500000000000000 : ℝ)) (alpha := (341159293899/196100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1068241903/5000000000 : ℝ)*X 0 0+(5399030087/10000000000 : ℝ)*X 0 1+(32874819/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673148367/5000000000 : ℝ)*X 1 0+(-441421743/2000000000 : ℝ)*X 1 1+(2629985583/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673148359/5000000000 : ℝ)*X 2 0+(2629985533/5000000000 : ℝ)*X 2 1+(-220710887/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177751061/5000000000 : ℝ)*X 0 0+(4217670691/10000000000 : ℝ)*X 0 1+(4497747789/10000000000 : ℝ)*X 0 2+(2177751061/5000000000 : ℝ)*X 1 0+(4217670691/10000000000 : ℝ)*X 1 1+(4497747789/10000000000 : ℝ)*X 1 2+(2177751061/5000000000 : ℝ)*X 2 0+(4217670691/10000000000 : ℝ)*X 2 1+(4497747789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-42729791/200000000 : ℝ)*X 0 0+(5260359747/10000000000 : ℝ)*X 0 1+(5398640369/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327726719/2500000000 : ℝ)*X 1 0+(-2068440433/10000000000 : ℝ)*X 1 1+(2699319929/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310907599/10000000000 : ℝ)*X 2 0+(1079727873/2000000000 : ℝ)*X 2 1+(-517110031/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355515603/10000000000 : ℝ)*X 0 0+(4496964541/10000000000 : ℝ)*X 0 1+(4218456683/10000000000 : ℝ)*X 0 2+(4355515603/10000000000 : ℝ)*X 1 0+(4496964541/10000000000 : ℝ)*X 1 1+(4218456683/10000000000 : ℝ)*X 1 2+(4355515603/10000000000 : ℝ)*X 2 0+(4496964541/10000000000 : ℝ)*X 2 1+(4218456683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (95752387121322785209356069/61281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (473871217/50000000000000 : ℝ)*(base19) + (950758057/100000000000000 : ℝ)*(base23) + (51006137/50000000000000 : ℝ)*(upper2) + (214879529/100000000000000 : ℝ)*(upper3) + (88894041/100000000000000 : ℝ)*(upper4) + (1345215049785009/25000000000000 : ℝ)*(major0) + (1345215049785009/25000000000000 : ℝ)*(major1) + (1345215049785009/25000000000000 : ℝ)*(major2) + (3595611742125651/50000000000000 : ℝ)*(sp0) + (7191245970878363/100000000000000 : ℝ)*(sp1) + (359562298393137/5000000000000 : ℝ)*(sp2) + (892614383957761/25000000000000 : ℝ)*(sp3) + (2929296187/12500000000000 : ℝ)*(sp4) + (7945872323/50000000000000 : ℝ)*(sp7) + (357047342757569/10000000000000 : ℝ)*(f.failure) + (7191246918620797/100000000000000 : ℝ)*(f.sum) + (20156567707847/4902500000000000000000000000 : ℝ)*base65 + (2311462072754938909/122562500000000000000000000000000 : ℝ)*base68 + (2946909337060063909/122562500000000000000000000000000 : ℝ)*base70 + (2592598836554438909/122562500000000000000000000000000 : ℝ)*base72 + (67834881582639/9805000000000000000000000000 : ℝ)*base73 + (1390758173622188909/122562500000000000000000000000000 : ℝ)*base76 + (33288039164313909/122562500000000000000000000000000 : ℝ)*base78 + (2925436471873313909/122562500000000000000000000000000 : ℝ)*base80 + (27215077195747/4902500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (597209/100000000000000000000 : ℝ)*base90 + (597209/100000000000000000000 : ℝ)*base92 + (597209/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1190366189331717451665732603/122562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74214017/20000000000000 : ℝ)*(base19) + (65375427/2500000000000 : ℝ)*(base23) + (4217141/25000000000000 : ℝ)*(lower2) + (535672563/100000000000000 : ℝ)*(lower4) + (77013819/50000000000000 : ℝ)*(upper5) + (5411133062354601/100000000000000 : ℝ)*(major0) + (5411133062354601/100000000000000 : ℝ)*(major1) + (5411133062354601/100000000000000 : ℝ)*(major2) + (14336076147/100000000000000 : ℝ)*(sp0) + (331323781/781250000000 : ℝ)*(sp2) + (451980653652181/6250000000000 : ℝ)*(sp4) + (3615852211720479/50000000000000 : ℝ)*(sp5) + (1446331954009999/20000000000000 : ℝ)*(sp6) + (3590561006454159/100000000000000 : ℝ)*(sp7) + (3590561006454159/100000000000000 : ℝ)*(f.failure) + (7231704794511043/100000000000000 : ℝ)*(f.sum) + (84313797776169/2451250000000000000000000000 : ℝ)*base66 + (11774397008703218299/490250000000000000000000000000000 : ℝ)*base67 + (1475395625017968299/490250000000000000000000000000000 : ℝ)*base69 + (1154685848861968299/490250000000000000000000000000000 : ℝ)*base71 + (611520767863/4902500000000000000000000000 : ℝ)*base74 + (2843611011497031701/490250000000000000000000000000000 : ℝ)*base76 + (1176020636116718299/490250000000000000000000000000000 : ℝ)*base77 + (3372141018082718299/490250000000000000000000000000000 : ℝ)*base79 + (9594753187293/4902500000000000000000000000 : ℝ)*base82 + (494199/1000000000000000000000 : ℝ)*base90 + (494199/1000000000000000000000 : ℝ)*base92 + (494199/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1205_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1205_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1205_s5_0 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-534248243/2500000000 : ℝ)*x 0 + (337081891/625000000 : ℝ)*x 1 + (658169569/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534248243/2500000000 : ℝ)^4199 ≤ (12991263715917/100000000000000 : ℝ)^3175 := by
    have hnat : (534248243 : ℕ)^4199*100000000000000^3175 ≤ 12991263715917^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534248243 2500000000 12991263715917 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337081891/625000000 : ℝ)^4199 ≤ (44195036173613/100000000000000 : ℝ)^3175 := by
    have hnat : (337081891 : ℕ)^4199*100000000000000^3175 ≤ 44195036173613^3175*625000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337081891 625000000 44195036173613 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658169569/1250000000 : ℝ)^4199 ≤ (21406850047987/50000000000000 : ℝ)^3175 := by
    have hnat : (658169569 : ℕ)^4199*50000000000000^3175 ≤ 21406850047987^3175*1250000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658169569 1250000000 21406850047987 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534248243/2500000000 : ℝ), (337081891/625000000 : ℝ), (658169569/1250000000 : ℝ)] ![(12991263715917/100000000000000 : ℝ), (44195036173613/100000000000000 : ℝ), (21406850047987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534248243/2500000000 : ℝ)|^4199 ≤ (12991263715917/100000000000000 : ℝ)^3175
        have hw : |(-534248243/2500000000 : ℝ)|=(534248243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337081891/625000000 : ℝ)|^4199 ≤ (44195036173613/100000000000000 : ℝ)^3175
        have hw : |(337081891/625000000 : ℝ)|=(337081891/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658169569/1250000000 : ℝ)|^4199 ≤ (21406850047987/50000000000000 : ℝ)^3175
        have hw : |(658169569/1250000000 : ℝ)|=(658169569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s5_1 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068970921/2000000000 : ℝ)*x 0 + (-220189759/1000000000 : ℝ)*x 1 + (1053071313/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068970921/2000000000 : ℝ)^4199 ≤ (43670671154459/100000000000000 : ℝ)^3175 := by
    have hnat : (1068970921 : ℕ)^4199*100000000000000^3175 ≤ 43670671154459^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068970921 2000000000 43670671154459 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220189759/1000000000 : ℝ)^4199 ≤ (3378907148793/25000000000000 : ℝ)^3175 := by
    have hnat : (220189759 : ℕ)^4199*25000000000000^3175 ≤ 3378907148793^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220189759 1000000000 3378907148793 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053071313/2000000000 : ℝ)^4199 ≤ (42813700235771/100000000000000 : ℝ)^3175 := by
    have hnat : (1053071313 : ℕ)^4199*100000000000000^3175 ≤ 42813700235771^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053071313 2000000000 42813700235771 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068970921/2000000000 : ℝ), (-220189759/1000000000 : ℝ), (1053071313/2000000000 : ℝ)] ![(43670671154459/100000000000000 : ℝ), (3378907148793/25000000000000 : ℝ), (42813700235771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068970921/2000000000 : ℝ)|^4199 ≤ (43670671154459/100000000000000 : ℝ)^3175
        have hw : |(1068970921/2000000000 : ℝ)|=(1068970921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-220189759/1000000000 : ℝ)|^4199 ≤ (3378907148793/25000000000000 : ℝ)^3175
        have hw : |(-220189759/1000000000 : ℝ)|=(220189759/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053071313/2000000000 : ℝ)|^4199 ≤ (42813700235771/100000000000000 : ℝ)^3175
        have hw : |(1053071313/2000000000 : ℝ)|=(1053071313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s5_2 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344854563/10000000000 : ℝ)*x 0 + (5265356679/10000000000 : ℝ)*x 1 + (-440379499/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344854563/10000000000 : ℝ)^4199 ≤ (5458833837577/12500000000000 : ℝ)^3175 := by
    have hnat : (5344854563 : ℕ)^4199*12500000000000^3175 ≤ 5458833837577^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344854563 10000000000 5458833837577 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265356679/10000000000 : ℝ)^4199 ≤ (42813701461691/100000000000000 : ℝ)^3175 := by
    have hnat : (5265356679 : ℕ)^4199*100000000000000^3175 ≤ 42813701461691^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265356679 10000000000 42813701461691 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440379499/2000000000 : ℝ)^4199 ≤ (1689453477997/12500000000000 : ℝ)^3175 := by
    have hnat : (440379499 : ℕ)^4199*12500000000000^3175 ≤ 1689453477997^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440379499 2000000000 1689453477997 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344854563/10000000000 : ℝ), (5265356679/10000000000 : ℝ), (-440379499/2000000000 : ℝ)] ![(5458833837577/12500000000000 : ℝ), (42813701461691/100000000000000 : ℝ), (1689453477997/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344854563/10000000000 : ℝ)|^4199 ≤ (5458833837577/12500000000000 : ℝ)^3175
        have hw : |(5344854563/10000000000 : ℝ)|=(5344854563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265356679/10000000000 : ℝ)|^4199 ≤ (42813701461691/100000000000000 : ℝ)^3175
        have hw : |(5265356679/10000000000 : ℝ)|=(5265356679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-440379499/2000000000 : ℝ)|^4199 ≤ (1689453477997/12500000000000 : ℝ)^3175
        have hw : |(-440379499/2000000000 : ℝ)|=(440379499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s5_3 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4355801769/10000000000 : ℝ)*x 0 + (4228816063/10000000000 : ℝ)*x 1 + (4486525421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355801769/10000000000 : ℝ)^4199 ≤ (6663316805097/20000000000000 : ℝ)^3175 := by
    have hnat : (4355801769 : ℕ)^4199*20000000000000^3175 ≤ 6663316805097^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355801769 10000000000 6663316805097 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228816063/10000000000 : ℝ)^4199 ≤ (16019059091041/50000000000000 : ℝ)^3175 := by
    have hnat : (4228816063 : ℕ)^4199*50000000000000^3175 ≤ 16019059091041^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228816063 10000000000 16019059091041 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486525421/10000000000 : ℝ)^4199 ≤ (17322648891029/50000000000000 : ℝ)^3175 := by
    have hnat : (4486525421 : ℕ)^4199*50000000000000^3175 ≤ 17322648891029^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486525421 10000000000 17322648891029 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355801769/10000000000 : ℝ), (4228816063/10000000000 : ℝ), (4486525421/10000000000 : ℝ)] ![(6663316805097/20000000000000 : ℝ), (16019059091041/50000000000000 : ℝ), (17322648891029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355801769/10000000000 : ℝ)|^4199 ≤ (6663316805097/20000000000000 : ℝ)^3175
        have hw : |(4355801769/10000000000 : ℝ)|=(4355801769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228816063/10000000000 : ℝ)|^4199 ≤ (16019059091041/50000000000000 : ℝ)^3175
        have hw : |(4228816063/10000000000 : ℝ)|=(4228816063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486525421/10000000000 : ℝ)|^4199 ≤ (17322648891029/50000000000000 : ℝ)^3175
        have hw : |(4486525421/10000000000 : ℝ)|=(4486525421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s5_4 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-213699799/1000000000 : ℝ)*x 0 + (1316421497/2500000000 : ℝ)*x 1 + (337061227/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213699799/1000000000 : ℝ)^4199 ≤ (3247826015033/25000000000000 : ℝ)^3175 := by
    have hnat : (213699799 : ℕ)^4199*25000000000000^3175 ≤ 3247826015033^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213699799 1000000000 3247826015033 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316421497/2500000000 : ℝ)^4199 ≤ (42817242781149/100000000000000 : ℝ)^3175 := by
    have hnat : (1316421497 : ℕ)^4199*100000000000000^3175 ≤ 42817242781149^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316421497 2500000000 42817242781149 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337061227/625000000 : ℝ)^4199 ≤ (22095726572333/50000000000000 : ℝ)^3175 := by
    have hnat : (337061227 : ℕ)^4199*50000000000000^3175 ≤ 22095726572333^3175*625000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337061227 625000000 22095726572333 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213699799/1000000000 : ℝ), (1316421497/2500000000 : ℝ), (337061227/625000000 : ℝ)] ![(3247826015033/25000000000000 : ℝ), (42817242781149/100000000000000 : ℝ), (22095726572333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213699799/1000000000 : ℝ)|^4199 ≤ (3247826015033/25000000000000 : ℝ)^3175
        have hw : |(-213699799/1000000000 : ℝ)|=(213699799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316421497/2500000000 : ℝ)|^4199 ≤ (42817242781149/100000000000000 : ℝ)^3175
        have hw : |(1316421497/2500000000 : ℝ)|=(1316421497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337061227/625000000 : ℝ)|^4199 ≤ (22095726572333/50000000000000 : ℝ)^3175
        have hw : |(337061227/625000000 : ℝ)|=(337061227/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s5_5 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312289849/10000000000 : ℝ)*x 0 + (-2074274607/10000000000 : ℝ)*x 1 + (539297963/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312289849/10000000000 : ℝ)^4199 ≤ (10829782445191/25000000000000 : ℝ)^3175 := by
    have hnat : (5312289849 : ℕ)^4199*25000000000000^3175 ≤ 10829782445191^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312289849 10000000000 10829782445191 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2074274607/10000000000 : ℝ)^4199 ≤ (6244708542921/50000000000000 : ℝ)^3175 := by
    have hnat : (2074274607 : ℕ)^4199*50000000000000^3175 ≤ 6244708542921^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074274607 10000000000 6244708542921 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539297963/1000000000 : ℝ)^4199 ≤ (44191453122991/100000000000000 : ℝ)^3175 := by
    have hnat : (539297963 : ℕ)^4199*100000000000000^3175 ≤ 44191453122991^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539297963 1000000000 44191453122991 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312289849/10000000000 : ℝ), (-2074274607/10000000000 : ℝ), (539297963/1000000000 : ℝ)] ![(10829782445191/25000000000000 : ℝ), (6244708542921/50000000000000 : ℝ), (44191453122991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312289849/10000000000 : ℝ)|^4199 ≤ (10829782445191/25000000000000 : ℝ)^3175
        have hw : |(5312289849/10000000000 : ℝ)|=(5312289849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2074274607/10000000000 : ℝ)|^4199 ≤ (6244708542921/50000000000000 : ℝ)^3175
        have hw : |(-2074274607/10000000000 : ℝ)|=(2074274607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539297963/1000000000 : ℝ)|^4199 ≤ (44191453122991/100000000000000 : ℝ)^3175
        have hw : |(539297963/1000000000 : ℝ)|=(539297963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s5_6 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312289849/10000000000 : ℝ)*x 0 + (5392979631/10000000000 : ℝ)*x 1 + (-1037137303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312289849/10000000000 : ℝ)^4199 ≤ (10829782445191/25000000000000 : ℝ)^3175 := by
    have hnat : (5312289849 : ℕ)^4199*25000000000000^3175 ≤ 10829782445191^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312289849 10000000000 10829782445191 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392979631/10000000000 : ℝ)^4199 ≤ (11047863283457/25000000000000 : ℝ)^3175 := by
    have hnat : (5392979631 : ℕ)^4199*25000000000000^3175 ≤ 11047863283457^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392979631 10000000000 11047863283457 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037137303/5000000000 : ℝ)^4199 ≤ (12489417077879/100000000000000 : ℝ)^3175 := by
    have hnat : (1037137303 : ℕ)^4199*100000000000000^3175 ≤ 12489417077879^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037137303 5000000000 12489417077879 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312289849/10000000000 : ℝ), (5392979631/10000000000 : ℝ), (-1037137303/5000000000 : ℝ)] ![(10829782445191/25000000000000 : ℝ), (11047863283457/25000000000000 : ℝ), (12489417077879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312289849/10000000000 : ℝ)|^4199 ≤ (10829782445191/25000000000000 : ℝ)^3175
        have hw : |(5312289849/10000000000 : ℝ)|=(5312289849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392979631/10000000000 : ℝ)|^4199 ≤ (11047863283457/25000000000000 : ℝ)^3175
        have hw : |(5392979631/10000000000 : ℝ)|=(5392979631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1037137303/5000000000 : ℝ)|^4199 ≤ (12489417077879/100000000000000 : ℝ)^3175
        have hw : |(-1037137303/5000000000 : ℝ)|=(1037137303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s5_7 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1088953011/2500000000 : ℝ)*x 0 + (2242931107/5000000000 : ℝ)*x 1 + (4229481637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088953011/2500000000 : ℝ)^4199 ≤ (16658343981999/50000000000000 : ℝ)^3175 := by
    have hnat : (1088953011 : ℕ)^4199*50000000000000^3175 ≤ 16658343981999^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088953011 2500000000 16658343981999 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242931107/5000000000 : ℝ)^4199 ≤ (2164907804743/6250000000000 : ℝ)^3175 := by
    have hnat : (2242931107 : ℕ)^4199*6250000000000^3175 ≤ 2164907804743^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242931107 5000000000 2164907804743 6250000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229481637/10000000000 : ℝ)^4199 ≤ (801119678401/2500000000000 : ℝ)^3175 := by
    have hnat : (4229481637 : ℕ)^4199*2500000000000^3175 ≤ 801119678401^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229481637 10000000000 801119678401 2500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088953011/2500000000 : ℝ), (2242931107/5000000000 : ℝ), (4229481637/10000000000 : ℝ)] ![(16658343981999/50000000000000 : ℝ), (2164907804743/6250000000000 : ℝ), (801119678401/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088953011/2500000000 : ℝ)|^4199 ≤ (16658343981999/50000000000000 : ℝ)^3175
        have hw : |(1088953011/2500000000 : ℝ)|=(1088953011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242931107/5000000000 : ℝ)|^4199 ≤ (2164907804743/6250000000000 : ℝ)^3175
        have hw : |(2242931107/5000000000 : ℝ)|=(2242931107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229481637/10000000000 : ℝ)|^4199 ≤ (801119678401/2500000000000 : ℝ)^3175
        have hw : |(4229481637/10000000000 : ℝ)|=(4229481637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1205_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2851/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2823/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1129/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1129/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1129/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1129/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1129/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1129/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1129/10000 : ℝ) ^ (8397/2048 : ℝ) ≤ (13060284920899761/100000000000000000000 : ℝ) := by
    have hpowers : (1129/10000 : ℝ)^8397 ≤ (13060284920899761/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1129 : ℕ)^8397*100000000000000000000^2048 ≤ 13060284920899761^2048*10000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1129 10000 13060284920899761 100000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1129/10000 : ℝ)) (X := (13060284920899761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8397/2048 : ℝ) ≤ (16890906484409713/50000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8397 ≤ (16890906484409713/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8397*50000000000000000000^2048 ≤ 16890906484409713^2048*20000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 16890906484409713 50000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (16890906484409713/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013060284920899761/50000000000000000000 : ℝ) ≤ (2500159252248599/2500000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (50013060284920899761/50000000000000000000 : ℝ)^2048 ≤ (2500159252248599/2500000000000000 : ℝ)^8397 := by
      have hnat : (50013060284920899761 : ℕ)^2048*2500000000000000^8397 ≤ 2500159252248599^8397*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013060284920899761 50000000000000000000 2500159252248599 2500000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500159252248599/2500000000000000 : ℝ)) (X := (50013060284920899761/50000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046842097889719187/100000000000000000000 : ℝ) ≤ (10001142260720293/10000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (100046842097889719187/100000000000000000000 : ℝ)^2048 ≤ (10001142260720293/10000000000000000 : ℝ)^8397 := by
      have hnat : (100046842097889719187 : ℕ)^2048*10000000000000000^8397 ≤ 10001142260720293^8397*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046842097889719187 100000000000000000000 10001142260720293 10000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001142260720293/10000000000000000 : ℝ)) (X := (100046842097889719187/100000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016890906484409713/25000000000000000000 : ℝ) ≤ (1000164751244619/1000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (25016890906484409713/25000000000000000000 : ℝ)^2048 ≤ (1000164751244619/1000000000000000 : ℝ)^8397 := by
      have hnat : (25016890906484409713 : ℕ)^2048*1000000000000000^8397 ≤ 1000164751244619^8397*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016890906484409713 25000000000000000000 1000164751244619 1000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000164751244619/1000000000000000 : ℝ)) (X := (25016890906484409713/25000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13060284920899761/100000000000000000000 : ℝ) ≤ ((736011685187943549/736250000000000000 : ℝ)+2*(505251725897/294500000000000 : ℝ)*(1129/10000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (736011685187943549/736250000000000000 : ℝ)+2*(505251725897/294500000000000 : ℝ)*(1129/10000 : ℝ)=(2500159252248599/2500000000000000 : ℝ) by norm_num, show 1+2*(13060284920899761/100000000000000000000 : ℝ)=(50013060284920899761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16890906484409713/50000000000000000000 : ℝ)+(13060284920899761/100000000000000000000 : ℝ) ≤ ((736011685187943549/736250000000000000 : ℝ)+(505251725897/294500000000000 : ℝ)*((2847/20000 : ℝ)+(1129/10000 : ℝ)))^(8397/2048 : ℝ) := by
    rw [show (736011685187943549/736250000000000000 : ℝ)+(505251725897/294500000000000 : ℝ)*((2847/20000 : ℝ)+(1129/10000 : ℝ))=(10001142260720293/10000000000000000 : ℝ) by norm_num, show 1+(16890906484409713/50000000000000000000 : ℝ)+(13060284920899761/100000000000000000000 : ℝ)=(100046842097889719187/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16890906484409713/50000000000000000000 : ℝ) ≤ ((736011685187943549/736250000000000000 : ℝ)+2*(505251725897/294500000000000 : ℝ)*(2847/20000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (736011685187943549/736250000000000000 : ℝ)+2*(505251725897/294500000000000 : ℝ)*(2847/20000 : ℝ)=(1000164751244619/1000000000000000 : ℝ) by norm_num, show 1+2*(16890906484409713/50000000000000000000 : ℝ)=(25016890906484409713/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (736011685187943549/736250000000000000 : ℝ)*(X 1 0+X 2 0)+(505251725897/294500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (736011685187943549/736250000000000000 : ℝ)) (alpha := (505251725897/294500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (736011685187943549/736250000000000000 : ℝ)*(X 0 1+X 2 1)+(505251725897/294500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (736011685187943549/736250000000000000 : ℝ)) (alpha := (505251725897/294500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (736011685187943549/736250000000000000 : ℝ)*(X 0 2+X 1 2)+(505251725897/294500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (736011685187943549/736250000000000000 : ℝ)) (alpha := (505251725897/294500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-534248243/2500000000 : ℝ)*X 0 0+(337081891/625000000 : ℝ)*X 0 1+(658169569/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068970921/2000000000 : ℝ)*X 1 0+(-220189759/1000000000 : ℝ)*X 1 1+(1053071313/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344854563/10000000000 : ℝ)*X 2 0+(5265356679/10000000000 : ℝ)*X 2 1+(-440379499/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355801769/10000000000 : ℝ)*X 0 0+(4228816063/10000000000 : ℝ)*X 0 1+(4486525421/10000000000 : ℝ)*X 0 2+(4355801769/10000000000 : ℝ)*X 1 0+(4228816063/10000000000 : ℝ)*X 1 1+(4486525421/10000000000 : ℝ)*X 1 2+(4355801769/10000000000 : ℝ)*X 2 0+(4228816063/10000000000 : ℝ)*X 2 1+(4486525421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-213699799/1000000000 : ℝ)*X 0 0+(1316421497/2500000000 : ℝ)*X 0 1+(337061227/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312289849/10000000000 : ℝ)*X 1 0+(-2074274607/10000000000 : ℝ)*X 1 1+(539297963/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312289849/10000000000 : ℝ)*X 2 0+(5392979631/10000000000 : ℝ)*X 2 1+(-1037137303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1088953011/2500000000 : ℝ)*X 0 0+(2242931107/5000000000 : ℝ)*X 0 1+(4229481637/10000000000 : ℝ)*X 0 2+(1088953011/2500000000 : ℝ)*X 1 0+(2242931107/5000000000 : ℝ)*X 1 1+(4229481637/10000000000 : ℝ)*X 1 2+(1088953011/2500000000 : ℝ)*X 2 0+(2242931107/5000000000 : ℝ)*X 2 1+(4229481637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (89962037227998457145463687/9203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (420991629/20000000000000 : ℝ)*(base19) + (50829187/2500000000000 : ℝ)*(base23) + (693269/12500000000000 : ℝ)*(lower2) + (32378731/25000000000000 : ℝ)*(upper3) + (262636001/100000000000000 : ℝ)*(upper5) + (2923963491565821/50000000000000 : ℝ)*(major0) + (2923963491565821/50000000000000 : ℝ)*(major1) + (2923963491565821/50000000000000 : ℝ)*(major2) + (3907694496600299/50000000000000 : ℝ)*(sp0) + (7815455627204111/100000000000000 : ℝ)*(sp1) + (312618227959791/4000000000000 : ℝ)*(sp2) + (485046183788567/12500000000000 : ℝ)*(sp3) + (34369480829/50000000000000 : ℝ)*(sp4) + (26437953753/100000000000000 : ℝ)*(sp7) + (3880395908262289/100000000000000 : ℝ)*(f.failure) + (1563091546432451/20000000000000 : ℝ)*(f.sum) + (2221185245563/7362500000000000000000000000 : ℝ)*base66 + (170144553372943771/36812500000000000000000000000000 : ℝ)*base68 + (654505433208131271/36812500000000000000000000000000 : ℝ)*base70 + (113184512081756271/36812500000000000000000000000000 : ℝ)*base72 + (29847849049187/7362500000000000000000000000 : ℝ)*base73 + (453688099328931229/36812500000000000000000000000000 : ℝ)*base75 + (176451474777381271/36812500000000000000000000000000 : ℝ)*base78 + (555710249525256271/36812500000000000000000000000000 : ℝ)*base80 + (16826191603413/7362500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2374871/1000000000000000000000 : ℝ)*base89 + (2374871/1000000000000000000000 : ℝ)*base91 + (2374871/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76289443857482454454386753/9203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1491803177/100000000000000 : ℝ)*(base19) + (1624909999/100000000000000 : ℝ)*(base23) + (166354143/100000000000000 : ℝ)*(upper3) + (12057441/20000000000000 : ℝ)*(lower4) + (168686361/100000000000000 : ℝ)*(upper5) + (1469537683796963/25000000000000 : ℝ)*(major0) + (1469537683796963/25000000000000 : ℝ)*(major1) + (1469537683796963/25000000000000 : ℝ)*(major2) + (40694168327/100000000000000 : ℝ)*(sp1) + (43894923879/100000000000000 : ℝ)*(sp2) + (7855850294660139/100000000000000 : ℝ)*(sp4) + (1963952027172159/25000000000000 : ℝ)*(sp5) + (7855804774826261/100000000000000 : ℝ)*(sp6) + (1950225449699193/50000000000000 : ℝ)*(sp7) + (1950225449699193/50000000000000 : ℝ)*(f.failure) + (7855850294660139/100000000000000 : ℝ)*(f.sum) + (2554483151953/7362500000000000000000000000 : ℝ)*base66 + (78407255732919187/18406250000000000000000000000000 : ℝ)*base67 + (118876934149606687/18406250000000000000000000000000 : ℝ)*base69 + (200908325236575437/18406250000000000000000000000000 : ℝ)*base71 + (13839976622147/7362500000000000000000000000 : ℝ)*base73 + (60689150654862063/18406250000000000000000000000000 : ℝ)*base76 + (102910088022106687/18406250000000000000000000000000 : ℝ)*base77 + (32912615957919187/18406250000000000000000000000000 : ℝ)*base79 + (39396076356269/14725000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3544273/500000000000000000000 : ℝ)*base90 + (3544273/500000000000000000000 : ℝ)*base92 + (3544273/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1205_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1205_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1205_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1205_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1205_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1205_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1205_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
