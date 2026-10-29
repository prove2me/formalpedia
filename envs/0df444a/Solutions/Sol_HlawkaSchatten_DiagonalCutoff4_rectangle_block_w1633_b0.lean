-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1633_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:00:47.179905+00:00
-- url     : https://prove2.me/submissions/ea5e5ebb-cccc-4ed0-8588-c41237470eec

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
theorem support_rectangle_w1633_s0_0 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1522961391/10000000000 : ℝ)*x 0 + (1451690153/2500000000 : ℝ)*x 1 + (2454883587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1522961391/10000000000 : ℝ)^4851 ≤ (1840894516647/20000000000000 : ℝ)^3827 := by
    have hnat : (1522961391 : ℕ)^4851*20000000000000^3827 ≤ 1840894516647^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522961391 10000000000 1840894516647 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1451690153/2500000000 : ℝ)^4851 ≤ (10041512304287/20000000000000 : ℝ)^3827 := by
    have hnat : (1451690153 : ℕ)^4851*20000000000000^3827 ≤ 10041512304287^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1451690153 2500000000 10041512304287 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2454883587/5000000000 : ℝ)^4851 ≤ (40587965880531/100000000000000 : ℝ)^3827 := by
    have hnat : (2454883587 : ℕ)^4851*100000000000000^3827 ≤ 40587965880531^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2454883587 5000000000 40587965880531 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1522961391/10000000000 : ℝ), (1451690153/2500000000 : ℝ), (2454883587/5000000000 : ℝ)] ![(1840894516647/20000000000000 : ℝ), (10041512304287/20000000000000 : ℝ), (40587965880531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1522961391/10000000000 : ℝ)|^4851 ≤ (1840894516647/20000000000000 : ℝ)^3827
        have hw : |(-1522961391/10000000000 : ℝ)|=(1522961391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1451690153/2500000000 : ℝ)|^4851 ≤ (10041512304287/20000000000000 : ℝ)^3827
        have hw : |(1451690153/2500000000 : ℝ)|=(1451690153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2454883587/5000000000 : ℝ)|^4851 ≤ (40587965880531/100000000000000 : ℝ)^3827
        have hw : |(2454883587/5000000000 : ℝ)|=(2454883587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s0_1 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5444336041/10000000000 : ℝ)*x 0 + (-1008550333/5000000000 : ℝ)*x 1 + (4909768841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5444336041/10000000000 : ℝ)^4851 ≤ (46269099091099/100000000000000 : ℝ)^3827 := by
    have hnat : (5444336041 : ℕ)^4851*100000000000000^3827 ≤ 46269099091099^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444336041 10000000000 46269099091099 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008550333/5000000000 : ℝ)^4851 ≤ (1642864694107/12500000000000 : ℝ)^3827 := by
    have hnat : (1008550333 : ℕ)^4851*12500000000000^3827 ≤ 1642864694107^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008550333 5000000000 1642864694107 12500000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4909768841/10000000000 : ℝ)^4851 ≤ (10146995837149/25000000000000 : ℝ)^3827 := by
    have hnat : (4909768841 : ℕ)^4851*25000000000000^3827 ≤ 10146995837149^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4909768841 10000000000 10146995837149 25000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5444336041/10000000000 : ℝ), (-1008550333/5000000000 : ℝ), (4909768841/10000000000 : ℝ)] ![(46269099091099/100000000000000 : ℝ), (1642864694107/12500000000000 : ℝ), (10146995837149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5444336041/10000000000 : ℝ)|^4851 ≤ (46269099091099/100000000000000 : ℝ)^3827
        have hw : |(5444336041/10000000000 : ℝ)|=(5444336041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1008550333/5000000000 : ℝ)|^4851 ≤ (1642864694107/12500000000000 : ℝ)^3827
        have hw : |(-1008550333/5000000000 : ℝ)|=(1008550333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4909768841/10000000000 : ℝ)|^4851 ≤ (10146995837149/25000000000000 : ℝ)^3827
        have hw : |(4909768841/10000000000 : ℝ)|=(4909768841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s0_2 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (54443369/100000000 : ℝ)*x 0 + (4909767557/10000000000 : ℝ)*x 1 + (-1008550587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54443369/100000000 : ℝ)^4851 ≤ (5783638543091/12500000000000 : ℝ)^3827 := by
    have hnat : (54443369 : ℕ)^4851*12500000000000^3827 ≤ 5783638543091^3827*100000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54443369 100000000 5783638543091 12500000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4909767557/10000000000 : ℝ)^4851 ≤ (40587969893889/100000000000000 : ℝ)^3827 := by
    have hnat : (4909767557 : ℕ)^4851*100000000000000^3827 ≤ 40587969893889^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4909767557 10000000000 40587969893889 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008550587/5000000000 : ℝ)^4851 ≤ (13142921748521/100000000000000 : ℝ)^3827 := by
    have hnat : (1008550587 : ℕ)^4851*100000000000000^3827 ≤ 13142921748521^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008550587 5000000000 13142921748521 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54443369/100000000 : ℝ), (4909767557/10000000000 : ℝ), (-1008550587/5000000000 : ℝ)] ![(5783638543091/12500000000000 : ℝ), (40587969893889/100000000000000 : ℝ), (13142921748521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54443369/100000000 : ℝ)|^4851 ≤ (5783638543091/12500000000000 : ℝ)^3827
        have hw : |(54443369/100000000 : ℝ)|=(54443369/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4909767557/10000000000 : ℝ)|^4851 ≤ (40587969893889/100000000000000 : ℝ)^3827
        have hw : |(4909767557/10000000000 : ℝ)|=(4909767557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1008550587/5000000000 : ℝ)|^4851 ≤ (13142921748521/100000000000000 : ℝ)^3827
        have hw : |(-1008550587/5000000000 : ℝ)|=(1008550587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s0_3 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2049325071/5000000000 : ℝ)*x 0 + (61573167/200000000 : ℝ)*x 1 + (1069955439/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049325071/5000000000 : ℝ)^4851 ≤ (32284509165283/100000000000000 : ℝ)^3827 := by
    have hnat : (2049325071 : ℕ)^4851*100000000000000^3827 ≤ 32284509165283^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049325071 5000000000 32284509165283 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61573167/200000000 : ℝ)^4851 ≤ (22462655528247/100000000000000 : ℝ)^3827 := by
    have hnat : (61573167 : ℕ)^4851*100000000000000^3827 ≤ 22462655528247^3827*200000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61573167 200000000 22462655528247 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1069955439/2000000000 : ℝ)^4851 ≤ (22626417645343/50000000000000 : ℝ)^3827 := by
    have hnat : (1069955439 : ℕ)^4851*50000000000000^3827 ≤ 22626417645343^3827*2000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069955439 2000000000 22626417645343 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2049325071/5000000000 : ℝ), (61573167/200000000 : ℝ), (1069955439/2000000000 : ℝ)] ![(32284509165283/100000000000000 : ℝ), (22462655528247/100000000000000 : ℝ), (22626417645343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2049325071/5000000000 : ℝ)|^4851 ≤ (32284509165283/100000000000000 : ℝ)^3827
        have hw : |(2049325071/5000000000 : ℝ)|=(2049325071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(61573167/200000000 : ℝ)|^4851 ≤ (22462655528247/100000000000000 : ℝ)^3827
        have hw : |(61573167/200000000 : ℝ)|=(61573167/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1069955439/2000000000 : ℝ)|^4851 ≤ (22626417645343/50000000000000 : ℝ)^3827
        have hw : |(1069955439/2000000000 : ℝ)|=(1069955439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s0_4 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-152545777/1000000000 : ℝ)*x 0 + (1233054471/2500000000 : ℝ)*x 1 + (1445881171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (152545777/1000000000 : ℝ)^4851 ≤ (461180070951/5000000000000 : ℝ)^3827 := by
    have hnat : (152545777 : ℕ)^4851*5000000000000^3827 ≤ 461180070951^3827*1000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152545777 1000000000 461180070951 5000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1233054471/2500000000 : ℝ)^4851 ≤ (20411682433281/50000000000000 : ℝ)^3827 := by
    have hnat : (1233054471 : ℕ)^4851*50000000000000^3827 ≤ 20411682433281^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233054471 2500000000 20411682433281 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1445881171/2500000000 : ℝ)^4851 ≤ (49953033704899/100000000000000 : ℝ)^3827 := by
    have hnat : (1445881171 : ℕ)^4851*100000000000000^3827 ≤ 49953033704899^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445881171 2500000000 49953033704899 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-152545777/1000000000 : ℝ), (1233054471/2500000000 : ℝ), (1445881171/2500000000 : ℝ)] ![(461180070951/5000000000000 : ℝ), (20411682433281/50000000000000 : ℝ), (49953033704899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-152545777/1000000000 : ℝ)|^4851 ≤ (461180070951/5000000000000 : ℝ)^3827
        have hw : |(-152545777/1000000000 : ℝ)|=(152545777/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1233054471/2500000000 : ℝ)|^4851 ≤ (20411682433281/50000000000000 : ℝ)^3827
        have hw : |(1233054471/2500000000 : ℝ)|=(1233054471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1445881171/2500000000 : ℝ)|^4851 ≤ (49953033704899/100000000000000 : ℝ)^3827
        have hw : |(1445881171/2500000000 : ℝ)|=(1445881171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s0_5 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599724849/5000000000 : ℝ)*x 0 + (-571671827/5000000000 : ℝ)*x 1 + (90367577/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599724849/5000000000 : ℝ)^4851 ≤ (43647099049697/100000000000000 : ℝ)^3827 := by
    have hnat : (2599724849 : ℕ)^4851*100000000000000^3827 ≤ 43647099049697^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599724849 5000000000 43647099049697 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571671827/5000000000 : ℝ)^4851 ≤ (6399864559731/100000000000000 : ℝ)^3827 := by
    have hnat : (571671827 : ℕ)^4851*100000000000000^3827 ≤ 6399864559731^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571671827 5000000000 6399864559731 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90367577/156250000 : ℝ)^4851 ≤ (780516193379/1562500000000 : ℝ)^3827 := by
    have hnat : (90367577 : ℕ)^4851*1562500000000^3827 ≤ 780516193379^3827*156250000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90367577 156250000 780516193379 1562500000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599724849/5000000000 : ℝ), (-571671827/5000000000 : ℝ), (90367577/156250000 : ℝ)] ![(43647099049697/100000000000000 : ℝ), (6399864559731/100000000000000 : ℝ), (780516193379/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599724849/5000000000 : ℝ)|^4851 ≤ (43647099049697/100000000000000 : ℝ)^3827
        have hw : |(2599724849/5000000000 : ℝ)|=(2599724849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-571671827/5000000000 : ℝ)|^4851 ≤ (6399864559731/100000000000000 : ℝ)^3827
        have hw : |(-571671827/5000000000 : ℝ)|=(571671827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90367577/156250000 : ℝ)|^4851 ≤ (780516193379/1562500000000 : ℝ)^3827
        have hw : |(90367577/156250000 : ℝ)|=(90367577/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s0_6 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199449749/10000000000 : ℝ)*x 0 + (289176237/500000000 : ℝ)*x 1 + (-1143343869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199449749/10000000000 : ℝ)^4851 ≤ (43647099592373/100000000000000 : ℝ)^3827 := by
    have hnat : (5199449749 : ℕ)^4851*100000000000000^3827 ≤ 43647099592373^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199449749 10000000000 43647099592373 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (289176237/500000000 : ℝ)^4851 ≤ (49953034317997/100000000000000 : ℝ)^3827 := by
    have hnat : (289176237 : ℕ)^4851*100000000000000^3827 ≤ 49953034317997^3827*500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289176237 500000000 49953034317997 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1143343869/10000000000 : ℝ)^4851 ≤ (6399866085207/100000000000000 : ℝ)^3827 := by
    have hnat : (1143343869 : ℕ)^4851*100000000000000^3827 ≤ 6399866085207^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143343869 10000000000 6399866085207 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199449749/10000000000 : ℝ), (289176237/500000000 : ℝ), (-1143343869/10000000000 : ℝ)] ![(43647099592373/100000000000000 : ℝ), (49953034317997/100000000000000 : ℝ), (6399866085207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199449749/10000000000 : ℝ)|^4851 ≤ (43647099592373/100000000000000 : ℝ)^3827
        have hw : |(5199449749/10000000000 : ℝ)|=(5199449749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(289176237/500000000 : ℝ)|^4851 ≤ (49953034317997/100000000000000 : ℝ)^3827
        have hw : |(289176237/500000000 : ℝ)|=(289176237/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1143343869/10000000000 : ℝ)|^4851 ≤ (6399866085207/100000000000000 : ℝ)^3827
        have hw : |(-1143343869/10000000000 : ℝ)|=(1143343869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s0_7 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4104971429/10000000000 : ℝ)*x 0 + (5292934409/10000000000 : ℝ)*x 1 + (1568744531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4104971429/10000000000 : ℝ)^4851 ≤ (8086909262169/25000000000000 : ℝ)^3827 := by
    have hnat : (4104971429 : ℕ)^4851*25000000000000^3827 ≤ 8086909262169^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4104971429 10000000000 8086909262169 25000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5292934409/10000000000 : ℝ)^4851 ≤ (44644225602171/100000000000000 : ℝ)^3827 := by
    have hnat : (5292934409 : ℕ)^4851*100000000000000^3827 ≤ 44644225602171^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292934409 10000000000 44644225602171 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1568744531/5000000000 : ℝ)^4851 ≤ (5752034334117/25000000000000 : ℝ)^3827 := by
    have hnat : (1568744531 : ℕ)^4851*25000000000000^3827 ≤ 5752034334117^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568744531 5000000000 5752034334117 25000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4104971429/10000000000 : ℝ), (5292934409/10000000000 : ℝ), (1568744531/5000000000 : ℝ)] ![(8086909262169/25000000000000 : ℝ), (44644225602171/100000000000000 : ℝ), (5752034334117/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4104971429/10000000000 : ℝ)|^4851 ≤ (8086909262169/25000000000000 : ℝ)^3827
        have hw : |(4104971429/10000000000 : ℝ)|=(4104971429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5292934409/10000000000 : ℝ)|^4851 ≤ (44644225602171/100000000000000 : ℝ)^3827
        have hw : |(5292934409/10000000000 : ℝ)|=(5292934409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1568744531/5000000000 : ℝ)|^4851 ≤ (5752034334117/25000000000000 : ℝ)^3827
        have hw : |(1568744531/5000000000 : ℝ)|=(1568744531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1633_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2253/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5931/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4847/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4847 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4847*1^1024 ≤ 0^1024*1^4847 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4847 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4847/1024 : ℝ) ≤ (1307348535529310991/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4847 ≤ (1307348535529310991/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4847*100000000000000000000^1024 ≤ 1307348535529310991^1024*5^4847 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1307348535529310991 100000000000000000000 4847 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1307348535529310991/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4847 := by
      have hnat : (1 : ℕ)^1024*1^4847 ≤ 1^4847*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101307348535529310991/100000000000000000000 : ℝ) ≤ (5013739179627989/5000000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (101307348535529310991/100000000000000000000 : ℝ)^1024 ≤ (5013739179627989/5000000000000000 : ℝ)^4847 := by
      have hnat : (101307348535529310991 : ℕ)^1024*5000000000000000^4847 ≤ 5013739179627989^4847*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101307348535529310991 100000000000000000000 5013739179627989 5000000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013739179627989/5000000000000000 : ℝ)) (X := (101307348535529310991/100000000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51307348535529310991/50000000000000000000 : ℝ) ≤ (2513739179627989/2500000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (51307348535529310991/50000000000000000000 : ℝ)^1024 ≤ (2513739179627989/2500000000000000 : ℝ)^4847 := by
      have hnat : (51307348535529310991 : ℕ)^1024*2500000000000000^4847 ≤ 2513739179627989^4847*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51307348535529310991 50000000000000000000 2513739179627989 2500000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2513739179627989/2500000000000000 : ℝ)) (X := (51307348535529310991/50000000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(13739179627989/2000000000000000 : ℝ)*(0 : ℝ))^(4847/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(13739179627989/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1307348535529310991/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(13739179627989/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4847/1024 : ℝ) := by
    rw [show (1 : ℝ)+(13739179627989/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5013739179627989/5000000000000000 : ℝ) by norm_num, show 1+(1307348535529310991/100000000000000000000 : ℝ)+(0 : ℝ)=(101307348535529310991/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1307348535529310991/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(13739179627989/2000000000000000 : ℝ)*(2/5 : ℝ))^(4847/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(13739179627989/2000000000000000 : ℝ)*(2/5 : ℝ)=(2513739179627989/2500000000000000 : ℝ) by norm_num, show 1+2*(1307348535529310991/100000000000000000000 : ℝ)=(51307348535529310991/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(13739179627989/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13739179627989/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(13739179627989/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13739179627989/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(13739179627989/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13739179627989/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1522961391/10000000000 : ℝ)*X 0 0+(1451690153/2500000000 : ℝ)*X 0 1+(2454883587/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5444336041/10000000000 : ℝ)*X 1 0+(-1008550333/5000000000 : ℝ)*X 1 1+(4909768841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((54443369/100000000 : ℝ)*X 2 0+(4909767557/10000000000 : ℝ)*X 2 1+(-1008550587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2049325071/5000000000 : ℝ)*X 0 0+(61573167/200000000 : ℝ)*X 0 1+(1069955439/2000000000 : ℝ)*X 0 2+(2049325071/5000000000 : ℝ)*X 1 0+(61573167/200000000 : ℝ)*X 1 1+(1069955439/2000000000 : ℝ)*X 1 2+(2049325071/5000000000 : ℝ)*X 2 0+(61573167/200000000 : ℝ)*X 2 1+(1069955439/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-152545777/1000000000 : ℝ)*X 0 0+(1233054471/2500000000 : ℝ)*X 0 1+(1445881171/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2599724849/5000000000 : ℝ)*X 1 0+(-571671827/5000000000 : ℝ)*X 1 1+(90367577/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5199449749/10000000000 : ℝ)*X 2 0+(289176237/500000000 : ℝ)*X 2 1+(-1143343869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4104971429/10000000000 : ℝ)*X 0 0+(5292934409/10000000000 : ℝ)*X 0 1+(1568744531/5000000000 : ℝ)*X 0 2+(4104971429/10000000000 : ℝ)*X 1 0+(5292934409/10000000000 : ℝ)*X 1 1+(1568744531/5000000000 : ℝ)*X 1 2+(4104971429/10000000000 : ℝ)*X 2 0+(5292934409/10000000000 : ℝ)*X 2 1+(1568744531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (961303190757978895591611/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (444893/2500000000000 : ℝ)*(base1) + (1761966207/100000000000000 : ℝ)*(base19) + (1937865897/100000000000000 : ℝ)*(base23) + (15989869/5000000000000 : ℝ)*(upper3) + (97595727/50000000000000 : ℝ)*(upper5) + (777585954927867/100000000000000 : ℝ)*(major0) + (777585954927867/100000000000000 : ℝ)*(major1) + (777585954927867/100000000000000 : ℝ)*(major2) + (557422170408079/50000000000000 : ℝ)*(sp0) + (1114851192657887/100000000000000 : ℝ)*(sp1) + (1114851016758197/100000000000000 : ℝ)*(sp2) + (440314789337877/100000000000000 : ℝ)*(sp3) + (8631603657/100000000000000 : ℝ)*(sp4) + (95691591/2500000000000 : ℝ)*(sp7) + (440318634797237/100000000000000 : ℝ)*(f.failure) + (557426477312047/50000000000000 : ℝ)*(f.sum) + (175035446669463/100000000000000000000000000000 : ℝ)*base65 + (95806049530537/200000000000000000000000000000 : ℝ)*base68 + (378892874269463/200000000000000000000000000000 : ℝ)*base69 + (1232815297069463/200000000000000000000000000000 : ℝ)*base71 + (82315507530537/100000000000000000000000000000 : ℝ)*base74 + (802066456869463/200000000000000000000000000000 : ℝ)*base75 + (927302510469463/200000000000000000000000000000 : ℝ)*base77 + (1087865101469463/200000000000000000000000000000 : ℝ)*base79 + (96609352430537/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (9857357/2000000000000000000000 : ℝ)*base90 + (9857357/2000000000000000000000 : ℝ)*base92 + (9857357/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12307038755763948311937/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (288438747/50000000000000 : ℝ)*(base19) + (292469973/50000000000000 : ℝ)*(base23) + (791063/25000000000000 : ℝ)*(base32) + (19661291/25000000000000 : ℝ)*(upper3) + (7085979/25000000000000 : ℝ)*(upper5) + (163860566499911/20000000000000 : ℝ)*(major0) + (163860566499911/20000000000000 : ℝ)*(major1) + (163860566499911/20000000000000 : ℝ)*(major2) + (1105889861/50000000000000 : ℝ)*(sp1) + (2138320111/100000000000000 : ℝ)*(sp2) + (1174664198201761/100000000000000 : ℝ)*(sp4) + (234932281908909/20000000000000 : ℝ)*(sp5) + (146832684367713/12500000000000 : ℝ)*(sp6) + (46394138158617/10000000000000 : ℝ)*(sp7) + (231970692375211/50000000000000 : ℝ)*(f.failure) + (1174664198201761/100000000000000 : ℝ)*(f.sum) + (50119297591021/20000000000000000000000000000 : ℝ)*base66 + (23431908551021/40000000000000000000000000000 : ℝ)*base68 + (84359139048979/40000000000000000000000000000 : ℝ)*base69 + (30267016071021/40000000000000000000000000000 : ℝ)*base72 + (32870443351021/20000000000000000000000000000 : ℝ)*base74 + (4016518471021/40000000000000000000000000000 : ℝ)*base76 + (147325823431021/40000000000000000000000000000 : ℝ)*base78 + (121940008928979/40000000000000000000000000000 : ℝ)*base79 + (3966207391021/20000000000000000000000000000 : ℝ)*base82 + (4984429/1000000000000000000000 : ℝ)*base89 + (4984429/1000000000000000000000 : ℝ)*base91 + (4984429/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1633_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2253/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5931/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1633_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1633_s1_0 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-818021901/5000000000 : ℝ)*x 0 + (1101930489/2000000000 : ℝ)*x 1 + (5133534129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (818021901/5000000000 : ℝ)^4851 ≤ (10079246377873/100000000000000 : ℝ)^3827 := by
    have hnat : (818021901 : ℕ)^4851*100000000000000^3827 ≤ 10079246377873^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818021901 5000000000 10079246377873 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101930489/2000000000 : ℝ)^4851 ≤ (23486925026367/50000000000000 : ℝ)^3827 := by
    have hnat : (1101930489 : ℕ)^4851*50000000000000^3827 ≤ 23486925026367^3827*2000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101930489 2000000000 23486925026367 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5133534129/10000000000 : ℝ)^4851 ≤ (42946903561163/100000000000000 : ℝ)^3827 := by
    have hnat : (5133534129 : ℕ)^4851*100000000000000^3827 ≤ 42946903561163^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133534129 10000000000 42946903561163 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-818021901/5000000000 : ℝ), (1101930489/2000000000 : ℝ), (5133534129/10000000000 : ℝ)] ![(10079246377873/100000000000000 : ℝ), (23486925026367/50000000000000 : ℝ), (42946903561163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-818021901/5000000000 : ℝ)|^4851 ≤ (10079246377873/100000000000000 : ℝ)^3827
        have hw : |(-818021901/5000000000 : ℝ)|=(818021901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1101930489/2000000000 : ℝ)|^4851 ≤ (23486925026367/50000000000000 : ℝ)^3827
        have hw : |(1101930489/2000000000 : ℝ)|=(1101930489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5133534129/10000000000 : ℝ)|^4851 ≤ (42946903561163/100000000000000 : ℝ)^3827
        have hw : |(5133534129/10000000000 : ℝ)|=(5133534129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s1_1 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5365308879/10000000000 : ℝ)*x 0 + (-366407977/2000000000 : ℝ)*x 1 + (2566766951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5365308879/10000000000 : ℝ)^4851 ≤ (45419433370667/100000000000000 : ℝ)^3827 := by
    have hnat : (5365308879 : ℕ)^4851*100000000000000^3827 ≤ 45419433370667^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365308879 10000000000 45419433370667 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366407977/2000000000 : ℝ)^4851 ≤ (5816832733537/50000000000000 : ℝ)^3827 := by
    have hnat : (366407977 : ℕ)^4851*50000000000000^3827 ≤ 5816832733537^3827*2000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366407977 2000000000 5816832733537 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566766951/5000000000 : ℝ)^4851 ≤ (1342090661061/3125000000000 : ℝ)^3827 := by
    have hnat : (2566766951 : ℕ)^4851*3125000000000^3827 ≤ 1342090661061^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566766951 5000000000 1342090661061 3125000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5365308879/10000000000 : ℝ), (-366407977/2000000000 : ℝ), (2566766951/5000000000 : ℝ)] ![(45419433370667/100000000000000 : ℝ), (5816832733537/50000000000000 : ℝ), (1342090661061/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5365308879/10000000000 : ℝ)|^4851 ≤ (45419433370667/100000000000000 : ℝ)^3827
        have hw : |(5365308879/10000000000 : ℝ)|=(5365308879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366407977/2000000000 : ℝ)|^4851 ≤ (5816832733537/50000000000000 : ℝ)^3827
        have hw : |(-366407977/2000000000 : ℝ)|=(366407977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566766951/5000000000 : ℝ)|^4851 ≤ (1342090661061/3125000000000 : ℝ)^3827
        have hw : |(2566766951/5000000000 : ℝ)|=(2566766951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s1_2 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5365309743/10000000000 : ℝ)*x 0 + (641691607/1250000000 : ℝ)*x 1 + (-183204011/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5365309743/10000000000 : ℝ)^4851 ≤ (5677430330227/12500000000000 : ℝ)^3827 := by
    have hnat : (5365309743 : ℕ)^4851*12500000000000^3827 ≤ 5677430330227^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365309743 10000000000 5677430330227 12500000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641691607/1250000000 : ℝ)^4851 ≤ (42946890061697/100000000000000 : ℝ)^3827 := by
    have hnat : (641691607 : ℕ)^4851*100000000000000^3827 ≤ 42946890061697^3827*1250000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641691607 1250000000 42946890061697 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (183204011/1000000000 : ℝ)^4851 ≤ (11633667278151/100000000000000 : ℝ)^3827 := by
    have hnat : (183204011 : ℕ)^4851*100000000000000^3827 ≤ 11633667278151^3827*1000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183204011 1000000000 11633667278151 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5365309743/10000000000 : ℝ), (641691607/1250000000 : ℝ), (-183204011/1000000000 : ℝ)] ![(5677430330227/12500000000000 : ℝ), (42946890061697/100000000000000 : ℝ), (11633667278151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5365309743/10000000000 : ℝ)|^4851 ≤ (5677430330227/12500000000000 : ℝ)^3827
        have hw : |(5365309743/10000000000 : ℝ)|=(5365309743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641691607/1250000000 : ℝ)|^4851 ≤ (42946890061697/100000000000000 : ℝ)^3827
        have hw : |(641691607/1250000000 : ℝ)|=(641691607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-183204011/1000000000 : ℝ)|^4851 ≤ (11633667278151/100000000000000 : ℝ)^3827
        have hw : |(-183204011/1000000000 : ℝ)|=(183204011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s1_3 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4185125523/10000000000 : ℝ)*x 0 + (932266389/2500000000 : ℝ)*x 1 + (4681370417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4185125523/10000000000 : ℝ)^4851 ≤ (33150346976321/100000000000000 : ℝ)^3827 := by
    have hnat : (4185125523 : ℕ)^4851*100000000000000^3827 ≤ 33150346976321^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185125523 10000000000 33150346976321 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (932266389/2500000000 : ℝ)^4851 ≤ (28639930472643/100000000000000 : ℝ)^3827 := by
    have hnat : (932266389 : ℕ)^4851*100000000000000^3827 ≤ 28639930472643^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932266389 2500000000 28639930472643 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4681370417/10000000000 : ℝ)^4851 ≤ (7641944505983/20000000000000 : ℝ)^3827 := by
    have hnat : (4681370417 : ℕ)^4851*20000000000000^3827 ≤ 7641944505983^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4681370417 10000000000 7641944505983 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4185125523/10000000000 : ℝ), (932266389/2500000000 : ℝ), (4681370417/10000000000 : ℝ)] ![(33150346976321/100000000000000 : ℝ), (28639930472643/100000000000000 : ℝ), (7641944505983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4185125523/10000000000 : ℝ)|^4851 ≤ (33150346976321/100000000000000 : ℝ)^3827
        have hw : |(4185125523/10000000000 : ℝ)|=(4185125523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(932266389/2500000000 : ℝ)|^4851 ≤ (28639930472643/100000000000000 : ℝ)^3827
        have hw : |(932266389/2500000000 : ℝ)|=(932266389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4681370417/10000000000 : ℝ)|^4851 ≤ (7641944505983/20000000000000 : ℝ)^3827
        have hw : |(4681370417/10000000000 : ℝ)|=(4681370417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s1_4 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1636225003/10000000000 : ℝ)*x 0 + (5137459193/10000000000 : ℝ)*x 1 + (5505669223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1636225003/10000000000 : ℝ)^4851 ≤ (5040330715869/50000000000000 : ℝ)^3827 := by
    have hnat : (1636225003 : ℕ)^4851*50000000000000^3827 ≤ 5040330715869^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1636225003 10000000000 5040330715869 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137459193/10000000000 : ℝ)^4851 ≤ (268678318559/625000000000 : ℝ)^3827 := by
    have hnat : (5137459193 : ℕ)^4851*625000000000^3827 ≤ 268678318559^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137459193 10000000000 268678318559 625000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505669223/10000000000 : ℝ)^4851 ≤ (2933175473443/6250000000000 : ℝ)^3827 := by
    have hnat : (5505669223 : ℕ)^4851*6250000000000^3827 ≤ 2933175473443^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505669223 10000000000 2933175473443 6250000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1636225003/10000000000 : ℝ), (5137459193/10000000000 : ℝ), (5505669223/10000000000 : ℝ)] ![(5040330715869/50000000000000 : ℝ), (268678318559/625000000000 : ℝ), (2933175473443/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1636225003/10000000000 : ℝ)|^4851 ≤ (5040330715869/50000000000000 : ℝ)^3827
        have hw : |(-1636225003/10000000000 : ℝ)|=(1636225003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137459193/10000000000 : ℝ)|^4851 ≤ (268678318559/625000000000 : ℝ)^3827
        have hw : |(5137459193/10000000000 : ℝ)|=(5137459193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5505669223/10000000000 : ℝ)|^4851 ≤ (2933175473443/6250000000000 : ℝ)^3827
        have hw : |(5505669223/10000000000 : ℝ)|=(5505669223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s1_5 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632468183/5000000000 : ℝ)*x 0 + (-729951829/5000000000 : ℝ)*x 1 + (5505669599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632468183/5000000000 : ℝ)^4851 ≤ (22172547302737/50000000000000 : ℝ)^3827 := by
    have hnat : (2632468183 : ℕ)^4851*50000000000000^3827 ≤ 22172547302737^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632468183 5000000000 22172547302737 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (729951829/5000000000 : ℝ)^4851 ≤ (8724093744161/100000000000000 : ℝ)^3827 := by
    have hnat : (729951829 : ℕ)^4851*100000000000000^3827 ≤ 8724093744161^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729951829 5000000000 8724093744161 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505669599/10000000000 : ℝ)^4851 ≤ (4693081163773/10000000000000 : ℝ)^3827 := by
    have hnat : (5505669599 : ℕ)^4851*10000000000000^3827 ≤ 4693081163773^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505669599 10000000000 4693081163773 10000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632468183/5000000000 : ℝ), (-729951829/5000000000 : ℝ), (5505669599/10000000000 : ℝ)] ![(22172547302737/50000000000000 : ℝ), (8724093744161/100000000000000 : ℝ), (4693081163773/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632468183/5000000000 : ℝ)|^4851 ≤ (22172547302737/50000000000000 : ℝ)^3827
        have hw : |(2632468183/5000000000 : ℝ)|=(2632468183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-729951829/5000000000 : ℝ)|^4851 ≤ (8724093744161/100000000000000 : ℝ)^3827
        have hw : |(-729951829/5000000000 : ℝ)|=(729951829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5505669599/10000000000 : ℝ)|^4851 ≤ (4693081163773/10000000000000 : ℝ)^3827
        have hw : |(5505669599/10000000000 : ℝ)|=(5505669599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s1_6 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264935679/10000000000 : ℝ)*x 0 + (5505669849/10000000000 : ℝ)*x 1 + (-364976067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264935679/10000000000 : ℝ)^4851 ≤ (2217254363539/5000000000000 : ℝ)^3827 := by
    have hnat : (5264935679 : ℕ)^4851*5000000000000^3827 ≤ 2217254363539^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264935679 10000000000 2217254363539 5000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5505669849/10000000000 : ℝ)^4851 ≤ (9386162867791/20000000000000 : ℝ)^3827 := by
    have hnat : (5505669849 : ℕ)^4851*20000000000000^3827 ≤ 9386162867791^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505669849 10000000000 9386162867791 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (364976067/2500000000 : ℝ)^4851 ≤ (4362049182383/50000000000000 : ℝ)^3827 := by
    have hnat : (364976067 : ℕ)^4851*50000000000000^3827 ≤ 4362049182383^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364976067 2500000000 4362049182383 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264935679/10000000000 : ℝ), (5505669849/10000000000 : ℝ), (-364976067/2500000000 : ℝ)] ![(2217254363539/5000000000000 : ℝ), (9386162867791/20000000000000 : ℝ), (4362049182383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264935679/10000000000 : ℝ)|^4851 ≤ (2217254363539/5000000000000 : ℝ)^3827
        have hw : |(5264935679/10000000000 : ℝ)|=(5264935679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5505669849/10000000000 : ℝ)|^4851 ≤ (9386162867791/20000000000000 : ℝ)^3827
        have hw : |(5505669849/10000000000 : ℝ)|=(5505669849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-364976067/2500000000 : ℝ)|^4851 ≤ (4362049182383/50000000000000 : ℝ)^3827
        have hw : |(-364976067/2500000000 : ℝ)|=(364976067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s1_7 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4185581161/10000000000 : ℝ)*x 0 + (1167858297/2500000000 : ℝ)*x 1 + (934787429/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4185581161/10000000000 : ℝ)^4851 ≤ (6630984369069/20000000000000 : ℝ)^3827 := by
    have hnat : (4185581161 : ℕ)^4851*20000000000000^3827 ≤ 6630984369069^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185581161 10000000000 6630984369069 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1167858297/2500000000 : ℝ)^4851 ≤ (4763367610411/12500000000000 : ℝ)^3827 := by
    have hnat : (1167858297 : ℕ)^4851*12500000000000^3827 ≤ 4763367610411^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167858297 2500000000 4763367610411 12500000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (934787429/2500000000 : ℝ)^4851 ≤ (5747627450489/20000000000000 : ℝ)^3827 := by
    have hnat : (934787429 : ℕ)^4851*20000000000000^3827 ≤ 5747627450489^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934787429 2500000000 5747627450489 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4185581161/10000000000 : ℝ), (1167858297/2500000000 : ℝ), (934787429/2500000000 : ℝ)] ![(6630984369069/20000000000000 : ℝ), (4763367610411/12500000000000 : ℝ), (5747627450489/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4185581161/10000000000 : ℝ)|^4851 ≤ (6630984369069/20000000000000 : ℝ)^3827
        have hw : |(4185581161/10000000000 : ℝ)|=(4185581161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1167858297/2500000000 : ℝ)|^4851 ≤ (4763367610411/12500000000000 : ℝ)^3827
        have hw : |(1167858297/2500000000 : ℝ)|=(1167858297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(934787429/2500000000 : ℝ)|^4851 ≤ (5747627450489/20000000000000 : ℝ)^3827
        have hw : |(934787429/2500000000 : ℝ)|=(934787429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1633_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5931/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2253/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1189/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8747/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5931/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2253/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5931/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2253/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5931/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2253/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5931/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2253/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5931/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2253/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5931/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2253/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2253/50000 : ℝ) ^ (4847/1024 : ℝ) ≤ (8489601509/20000000000000000 : ℝ) := by
    have hpowers : (2253/50000 : ℝ)^4847 ≤ (8489601509/20000000000000000 : ℝ)^1024 := by
      have hnat : (2253 : ℕ)^4847*20000000000000000^1024 ≤ 8489601509^1024*50000^4847 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2253 50000 8489601509 20000000000000000 4847 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2253/50000 : ℝ)) (X := (8489601509/20000000000000000 : ℝ)) (by norm_num) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5931/25000 : ℝ) ^ (4847/1024 : ℝ) ≤ (110284747917462317/100000000000000000000 : ℝ) := by
    have hpowers : (5931/25000 : ℝ)^4847 ≤ (110284747917462317/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5931 : ℕ)^4847*100000000000000000000^1024 ≤ 110284747917462317^1024*25000^4847 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5931 25000 110284747917462317 100000000000000000000 4847 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5931/25000 : ℝ)) (X := (110284747917462317/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000008489601509/10000000000000000 : ℝ) ≤ (5000000896776257/5000000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (10000008489601509/10000000000000000 : ℝ)^1024 ≤ (5000000896776257/5000000000000000 : ℝ)^4847 := by
      have hnat : (10000008489601509 : ℕ)^1024*5000000000000000^4847 ≤ 5000000896776257^4847*10000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000008489601509 10000000000000000 5000000896776257 5000000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000896776257/5000000000000000 : ℝ)) (X := (10000008489601509/10000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100110327195925007317/100000000000000000000 : ℝ) ≤ (625145613170627/625000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (100110327195925007317/100000000000000000000 : ℝ)^1024 ≤ (625145613170627/625000000000000 : ℝ)^4847 := by
      have hnat : (100110327195925007317 : ℕ)^1024*625000000000000^4847 ≤ 625145613170627^4847*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100110327195925007317 100000000000000000000 625145613170627 625000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625145613170627/625000000000000 : ℝ)) (X := (100110327195925007317/100000000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50110284747917462317/50000000000000000000 : ℝ) ≤ (200093156558151/200000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (50110284747917462317/50000000000000000000 : ℝ)^1024 ≤ (200093156558151/200000000000000 : ℝ)^4847 := by
      have hnat : (50110284747917462317 : ℕ)^1024*200000000000000^4847 ≤ 200093156558151^4847*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50110284747917462317 50000000000000000000 200093156558151 200000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200093156558151/200000000000000 : ℝ)) (X := (50110284747917462317/50000000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8489601509/20000000000000000 : ℝ) ≤ ((16013254531474035153/16015000000000000000 : ℝ)+2*(1164008588759/960900000000000 : ℝ)*(2253/50000 : ℝ))^(4847/1024 : ℝ) := by
    rw [show (16013254531474035153/16015000000000000000 : ℝ)+2*(1164008588759/960900000000000 : ℝ)*(2253/50000 : ℝ)=(5000000896776257/5000000000000000 : ℝ) by norm_num, show 1+2*(8489601509/20000000000000000 : ℝ)=(10000008489601509/10000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(110284747917462317/100000000000000000000 : ℝ)+(8489601509/20000000000000000 : ℝ) ≤ ((16013254531474035153/16015000000000000000 : ℝ)+(1164008588759/960900000000000 : ℝ)*((5931/25000 : ℝ)+(2253/50000 : ℝ)))^(4847/1024 : ℝ) := by
    rw [show (16013254531474035153/16015000000000000000 : ℝ)+(1164008588759/960900000000000 : ℝ)*((5931/25000 : ℝ)+(2253/50000 : ℝ))=(625145613170627/625000000000000 : ℝ) by norm_num, show 1+(110284747917462317/100000000000000000000 : ℝ)+(8489601509/20000000000000000 : ℝ)=(100110327195925007317/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(110284747917462317/100000000000000000000 : ℝ) ≤ ((16013254531474035153/16015000000000000000 : ℝ)+2*(1164008588759/960900000000000 : ℝ)*(5931/25000 : ℝ))^(4847/1024 : ℝ) := by
    rw [show (16013254531474035153/16015000000000000000 : ℝ)+2*(1164008588759/960900000000000 : ℝ)*(5931/25000 : ℝ)=(200093156558151/200000000000000 : ℝ) by norm_num, show 1+2*(110284747917462317/100000000000000000000 : ℝ)=(50110284747917462317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16013254531474035153/16015000000000000000 : ℝ)*(X 1 0+X 2 0)+(1164008588759/960900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (2253/50000 : ℝ)) (hi := (5931/25000 : ℝ)) (c := (16013254531474035153/16015000000000000000 : ℝ)) (alpha := (1164008588759/960900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16013254531474035153/16015000000000000000 : ℝ)*(X 0 1+X 2 1)+(1164008588759/960900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (2253/50000 : ℝ)) (hi := (5931/25000 : ℝ)) (c := (16013254531474035153/16015000000000000000 : ℝ)) (alpha := (1164008588759/960900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16013254531474035153/16015000000000000000 : ℝ)*(X 0 2+X 1 2)+(1164008588759/960900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (2253/50000 : ℝ)) (hi := (5931/25000 : ℝ)) (c := (16013254531474035153/16015000000000000000 : ℝ)) (alpha := (1164008588759/960900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-818021901/5000000000 : ℝ)*X 0 0+(1101930489/2000000000 : ℝ)*X 0 1+(5133534129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5365308879/10000000000 : ℝ)*X 1 0+(-366407977/2000000000 : ℝ)*X 1 1+(2566766951/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5365309743/10000000000 : ℝ)*X 2 0+(641691607/1250000000 : ℝ)*X 2 1+(-183204011/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4185125523/10000000000 : ℝ)*X 0 0+(932266389/2500000000 : ℝ)*X 0 1+(4681370417/10000000000 : ℝ)*X 0 2+(4185125523/10000000000 : ℝ)*X 1 0+(932266389/2500000000 : ℝ)*X 1 1+(4681370417/10000000000 : ℝ)*X 1 2+(4185125523/10000000000 : ℝ)*X 2 0+(932266389/2500000000 : ℝ)*X 2 1+(4681370417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1636225003/10000000000 : ℝ)*X 0 0+(5137459193/10000000000 : ℝ)*X 0 1+(5505669223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2632468183/5000000000 : ℝ)*X 1 0+(-729951829/5000000000 : ℝ)*X 1 1+(5505669599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5264935679/10000000000 : ℝ)*X 2 0+(5505669849/10000000000 : ℝ)*X 2 1+(-364976067/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4185581161/10000000000 : ℝ)*X 0 0+(1167858297/2500000000 : ℝ)*X 0 1+(934787429/2500000000 : ℝ)*X 0 2+(4185581161/10000000000 : ℝ)*X 1 0+(1167858297/2500000000 : ℝ)*X 1 1+(934787429/2500000000 : ℝ)*X 1 2+(4185581161/10000000000 : ℝ)*X 2 0+(1167858297/2500000000 : ℝ)*X 2 1+(934787429/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (167448323851761078859623321/20018750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (249990653/50000000000000 : ℝ)*(base1) + (141920627/12500000000000 : ℝ)*(base19) + (1563514011/100000000000000 : ℝ)*(base23) + (74699303/50000000000000 : ℝ)*(upper3) + (41182843/50000000000000 : ℝ)*(upper5) + (46360372767277/2500000000000 : ℝ)*(major0) + (46360372767277/2500000000000 : ℝ)*(major1) + (46360372767277/2500000000000 : ℝ)*(major2) + (2658740035413863/100000000000000 : ℝ)*(sp0) + (1329370356903689/50000000000000 : ℝ)*(sp1) + (1329370142829191/50000000000000 : ℝ)*(sp2) + (262521268361753/25000000000000 : ℝ)*(sp3) + (2313739837/100000000000000 : ℝ)*(sp4) + (132497643/6250000000000 : ℝ)*(sp7) + (65630480836913/6250000000000 : ℝ)*(f.failure) + (2658741849172393/100000000000000 : ℝ)*(f.sum) + (36904200898681/9609000000000000000000000000 : ℝ)*base65 + (1693263526173815143/120112500000000000000000000000000 : ℝ)*base67 + (1588144453586540143/120112500000000000000000000000000 : ℝ)*base69 + (1049063732848490143/120112500000000000000000000000000 : ℝ)*base71 + (9437861561677/960900000000000000000000000 : ℝ)*base73 + (445807078004015143/120112500000000000000000000000000 : ℝ)*base75 + (1405184495680040143/120112500000000000000000000000000 : ℝ)*base77 + (862327363232015143/120112500000000000000000000000000 : ℝ)*base79 + (9023459800127/1201125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (269207/125000000000000000000 : ℝ)*base89 + (269207/125000000000000000000 : ℝ)*base91 + (269207/125000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1069059640616864839652871573/200187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1134070073/100000000000000 : ℝ)*(base19) + (881492033/100000000000000 : ℝ)*(base23) + (5802049/10000000000000 : ℝ)*(upper2) + (300378409/100000000000000 : ℝ)*(upper3) + (947117659402453/50000000000000 : ℝ)*(major0) + (947117659402453/50000000000000 : ℝ)*(major1) + (947117659402453/50000000000000 : ℝ)*(major2) + (104607509/1250000000000 : ℝ)*(sp1) + (1981942699/25000000000000 : ℝ)*(sp2) + (46918221/50000000000000 : ℝ)*(sp3) + (678958479477411/25000000000000 : ℝ)*(sp4) + (2715824415238851/100000000000000 : ℝ)*(sp5) + (84869534645213/3125000000000 : ℝ)*(sp6) + (536318223926999/50000000000000 : ℝ)*(sp7) + (26815913542261/2500000000000 : ℝ)*(f.failure) + (678958479477411/25000000000000 : ℝ)*(f.sum) + (7916914830193/24022500000000000000000000000 : ℝ)*base66 + (8216581770177640927/2402250000000000000000000000000000 : ℝ)*base67 + (24568330393919140927/2402250000000000000000000000000000 : ℝ)*base69 + (10576180969703140927/2402250000000000000000000000000000 : ℝ)*base71 + (9305189935711/12011250000000000000000000000 : ℝ)*base73 + (7199309603570890927/2402250000000000000000000000000000 : ℝ)*base75 + (3813453027275359073/2402250000000000000000000000000000 : ℝ)*base78 + (2851956661524640927/2402250000000000000000000000000000 : ℝ)*base79 + (53654095100281/12011250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (140621/50000000000000000000 : ℝ)*base90 + (140621/50000000000000000000 : ℝ)*base92 + (140621/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1633_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5931/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2253/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1189/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8747/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1633_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1633_s2_0 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-823546683/5000000000 : ℝ)*x 0 + (5457376337/10000000000 : ℝ)*x 1 + (5178543899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823546683/5000000000 : ℝ)^4851 ≤ (10165612353247/100000000000000 : ℝ)^3827 := by
    have hnat : (823546683 : ℕ)^4851*100000000000000^3827 ≤ 10165612353247^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823546683 5000000000 10165612353247 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457376337/10000000000 : ℝ)^4851 ≤ (46409621454703/100000000000000 : ℝ)^3827 := by
    have hnat : (5457376337 : ℕ)^4851*100000000000000^3827 ≤ 46409621454703^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457376337 10000000000 46409621454703 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178543899/10000000000 : ℝ)^4851 ≤ (21712383089377/50000000000000 : ℝ)^3827 := by
    have hnat : (5178543899 : ℕ)^4851*50000000000000^3827 ≤ 21712383089377^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178543899 10000000000 21712383089377 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-823546683/5000000000 : ℝ), (5457376337/10000000000 : ℝ), (5178543899/10000000000 : ℝ)] ![(10165612353247/100000000000000 : ℝ), (46409621454703/100000000000000 : ℝ), (21712383089377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-823546683/5000000000 : ℝ)|^4851 ≤ (10165612353247/100000000000000 : ℝ)^3827
        have hw : |(-823546683/5000000000 : ℝ)|=(823546683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457376337/10000000000 : ℝ)|^4851 ≤ (46409621454703/100000000000000 : ℝ)^3827
        have hw : |(5457376337/10000000000 : ℝ)|=(5457376337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178543899/10000000000 : ℝ)|^4851 ≤ (21712383089377/50000000000000 : ℝ)^3827
        have hw : |(5178543899/10000000000 : ℝ)|=(5178543899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s2_1 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675779001/5000000000 : ℝ)*x 0 + (-895436367/5000000000 : ℝ)*x 1 + (1294635983/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675779001/5000000000 : ℝ)^4851 ≤ (45271930266173/100000000000000 : ℝ)^3827 := by
    have hnat : (2675779001 : ℕ)^4851*100000000000000^3827 ≤ 45271930266173^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675779001 5000000000 45271930266173 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895436367/5000000000 : ℝ)^4851 ≤ (1412912899263/12500000000000 : ℝ)^3827 := by
    have hnat : (895436367 : ℕ)^4851*12500000000000^3827 ≤ 1412912899263^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895436367 5000000000 1412912899263 12500000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294635983/2500000000 : ℝ)^4851 ≤ (542809581619/1250000000000 : ℝ)^3827 := by
    have hnat : (1294635983 : ℕ)^4851*1250000000000^3827 ≤ 542809581619^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294635983 2500000000 542809581619 1250000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675779001/5000000000 : ℝ), (-895436367/5000000000 : ℝ), (1294635983/2500000000 : ℝ)] ![(45271930266173/100000000000000 : ℝ), (1412912899263/12500000000000 : ℝ), (542809581619/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675779001/5000000000 : ℝ)|^4851 ≤ (45271930266173/100000000000000 : ℝ)^3827
        have hw : |(2675779001/5000000000 : ℝ)|=(2675779001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-895436367/5000000000 : ℝ)|^4851 ≤ (1412912899263/12500000000000 : ℝ)^3827
        have hw : |(-895436367/5000000000 : ℝ)|=(895436367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294635983/2500000000 : ℝ)|^4851 ≤ (542809581619/1250000000000 : ℝ)^3827
        have hw : |(1294635983/2500000000 : ℝ)|=(1294635983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s2_2 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070311601/2000000000 : ℝ)*x 0 + (5178543901/10000000000 : ℝ)*x 1 + (-1790872769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070311601/2000000000 : ℝ)^4851 ≤ (45271930298343/100000000000000 : ℝ)^3827 := by
    have hnat : (1070311601 : ℕ)^4851*100000000000000^3827 ≤ 45271930298343^3827*2000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070311601 2000000000 45271930298343 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178543901/10000000000 : ℝ)^4851 ≤ (43424766200013/100000000000000 : ℝ)^3827 := by
    have hnat : (5178543901 : ℕ)^4851*100000000000000^3827 ≤ 43424766200013^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178543901 10000000000 43424766200013 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1790872769/10000000000 : ℝ)^4851 ≤ (11303303474119/100000000000000 : ℝ)^3827 := by
    have hnat : (1790872769 : ℕ)^4851*100000000000000^3827 ≤ 11303303474119^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1790872769 10000000000 11303303474119 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070311601/2000000000 : ℝ), (5178543901/10000000000 : ℝ), (-1790872769/10000000000 : ℝ)] ![(45271930298343/100000000000000 : ℝ), (43424766200013/100000000000000 : ℝ), (11303303474119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070311601/2000000000 : ℝ)|^4851 ≤ (45271930298343/100000000000000 : ℝ)^3827
        have hw : |(1070311601/2000000000 : ℝ)|=(1070311601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178543901/10000000000 : ℝ)|^4851 ≤ (43424766200013/100000000000000 : ℝ)^3827
        have hw : |(5178543901/10000000000 : ℝ)|=(5178543901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1790872769/10000000000 : ℝ)|^4851 ≤ (11303303474119/100000000000000 : ℝ)^3827
        have hw : |(-1790872769/10000000000 : ℝ)|=(1790872769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s2_3 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1048332147/2500000000 : ℝ)*x 0 + (770276903/2000000000 : ℝ)*x 1 + (2278683459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048332147/2500000000 : ℝ)^4851 ≤ (33232730880687/100000000000000 : ℝ)^3827 := by
    have hnat : (1048332147 : ℕ)^4851*100000000000000^3827 ≤ 33232730880687^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048332147 2500000000 33232730880687 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (770276903/2000000000 : ℝ)^4851 ≤ (29835914087929/100000000000000 : ℝ)^3827 := by
    have hnat : (770276903 : ℕ)^4851*100000000000000^3827 ≤ 29835914087929^3827*2000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770276903 2000000000 29835914087929 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2278683459/5000000000 : ℝ)^4851 ≤ (36931355012149/100000000000000 : ℝ)^3827 := by
    have hnat : (2278683459 : ℕ)^4851*100000000000000^3827 ≤ 36931355012149^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278683459 5000000000 36931355012149 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048332147/2500000000 : ℝ), (770276903/2000000000 : ℝ), (2278683459/5000000000 : ℝ)] ![(33232730880687/100000000000000 : ℝ), (29835914087929/100000000000000 : ℝ), (36931355012149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048332147/2500000000 : ℝ)|^4851 ≤ (33232730880687/100000000000000 : ℝ)^3827
        have hw : |(1048332147/2500000000 : ℝ)|=(1048332147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(770276903/2000000000 : ℝ)|^4851 ≤ (29835914087929/100000000000000 : ℝ)^3827
        have hw : |(770276903/2000000000 : ℝ)|=(770276903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2278683459/5000000000 : ℝ)|^4851 ≤ (36931355012149/100000000000000 : ℝ)^3827
        have hw : |(2278683459/5000000000 : ℝ)|=(2278683459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s2_4 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-411791659/2500000000 : ℝ)*x 0 + (5180707951/10000000000 : ℝ)*x 1 + (5455189027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411791659/2500000000 : ℝ)^4851 ≤ (5083092783707/50000000000000 : ℝ)^3827 := by
    have hnat : (411791659 : ℕ)^4851*50000000000000^3827 ≤ 5083092783707^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411791659 2500000000 5083092783707 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180707951/10000000000 : ℝ)^4851 ≤ (21723884857627/50000000000000 : ℝ)^3827 := by
    have hnat : (5180707951 : ℕ)^4851*50000000000000^3827 ≤ 21723884857627^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180707951 10000000000 21723884857627 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455189027/10000000000 : ℝ)^4851 ≤ (46386044702277/100000000000000 : ℝ)^3827 := by
    have hnat : (5455189027 : ℕ)^4851*100000000000000^3827 ≤ 46386044702277^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455189027 10000000000 46386044702277 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411791659/2500000000 : ℝ), (5180707951/10000000000 : ℝ), (5455189027/10000000000 : ℝ)] ![(5083092783707/50000000000000 : ℝ), (21723884857627/50000000000000 : ℝ), (46386044702277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411791659/2500000000 : ℝ)|^4851 ≤ (5083092783707/50000000000000 : ℝ)^3827
        have hw : |(-411791659/2500000000 : ℝ)|=(411791659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180707951/10000000000 : ℝ)|^4851 ≤ (21723884857627/50000000000000 : ℝ)^3827
        have hw : |(5180707951/10000000000 : ℝ)|=(5180707951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455189027/10000000000 : ℝ)|^4851 ≤ (46386044702277/100000000000000 : ℝ)^3827
        have hw : |(5455189027/10000000000 : ℝ)|=(5455189027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s2_5 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659653197/1250000000 : ℝ)*x 0 + (-151422747/1000000000 : ℝ)*x 1 + (5455189143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659653197/1250000000 : ℝ)^4851 ≤ (44476340207637/100000000000000 : ℝ)^3827 := by
    have hnat : (659653197 : ℕ)^4851*100000000000000^3827 ≤ 44476340207637^3827*1250000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659653197 1250000000 44476340207637 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151422747/1000000000 : ℝ)^4851 ≤ (913761382871/10000000000000 : ℝ)^3827 := by
    have hnat : (151422747 : ℕ)^4851*10000000000000^3827 ≤ 913761382871^3827*1000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151422747 1000000000 913761382871 10000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455189143/10000000000 : ℝ)^4851 ≤ (579825574407/1250000000000 : ℝ)^3827 := by
    have hnat : (5455189143 : ℕ)^4851*1250000000000^3827 ≤ 579825574407^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455189143 10000000000 579825574407 1250000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659653197/1250000000 : ℝ), (-151422747/1000000000 : ℝ), (5455189143/10000000000 : ℝ)] ![(44476340207637/100000000000000 : ℝ), (913761382871/10000000000000 : ℝ), (579825574407/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659653197/1250000000 : ℝ)|^4851 ≤ (44476340207637/100000000000000 : ℝ)^3827
        have hw : |(659653197/1250000000 : ℝ)|=(659653197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-151422747/1000000000 : ℝ)|^4851 ≤ (913761382871/10000000000000 : ℝ)^3827
        have hw : |(-151422747/1000000000 : ℝ)|=(151422747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455189143/10000000000 : ℝ)|^4851 ≤ (579825574407/1250000000000 : ℝ)^3827
        have hw : |(5455189143/10000000000 : ℝ)|=(5455189143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s2_6 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277226469/10000000000 : ℝ)*x 0 + (5455188133/10000000000 : ℝ)*x 1 + (-302845529/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277226469/10000000000 : ℝ)^4851 ≤ (44476349747621/100000000000000 : ℝ)^3827 := by
    have hnat : (5277226469 : ℕ)^4851*100000000000000^3827 ≤ 44476349747621^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277226469 10000000000 44476349747621 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5455188133/10000000000 : ℝ)^4851 ≤ (1855441402659/4000000000000 : ℝ)^3827 := by
    have hnat : (5455188133 : ℕ)^4851*4000000000000^3827 ≤ 1855441402659^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455188133 10000000000 1855441402659 4000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302845529/2000000000 : ℝ)^4851 ≤ (1827523033463/20000000000000 : ℝ)^3827 := by
    have hnat : (302845529 : ℕ)^4851*20000000000000^3827 ≤ 1827523033463^3827*2000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302845529 2000000000 1827523033463 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277226469/10000000000 : ℝ), (5455188133/10000000000 : ℝ), (-302845529/2000000000 : ℝ)] ![(44476349747621/100000000000000 : ℝ), (1855441402659/4000000000000 : ℝ), (1827523033463/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277226469/10000000000 : ℝ)|^4851 ≤ (44476349747621/100000000000000 : ℝ)^3827
        have hw : |(5277226469/10000000000 : ℝ)|=(5277226469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5455188133/10000000000 : ℝ)|^4851 ≤ (1855441402659/4000000000000 : ℝ)^3827
        have hw : |(5455188133/10000000000 : ℝ)|=(5455188133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-302845529/2000000000 : ℝ)|^4851 ≤ (1827523033463/20000000000000 : ℝ)^3827
        have hw : |(-302845529/2000000000 : ℝ)|=(302845529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s2_7 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4193514783/10000000000 : ℝ)*x 0 + (455188957/1000000000 : ℝ)*x 1 + (385692171/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193514783/10000000000 : ℝ)^4851 ≤ (6646920269961/20000000000000 : ℝ)^3827 := by
    have hnat : (4193514783 : ℕ)^4851*20000000000000^3827 ≤ 6646920269961^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193514783 10000000000 6646920269961 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (455188957/1000000000 : ℝ)^4851 ≤ (4609387608271/12500000000000 : ℝ)^3827 := by
    have hnat : (455188957 : ℕ)^4851*12500000000000^3827 ≤ 4609387608271^3827*1000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455188957 1000000000 4609387608271 12500000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385692171/1000000000 : ℝ)^4851 ≤ (14945148884239/50000000000000 : ℝ)^3827 := by
    have hnat : (385692171 : ℕ)^4851*50000000000000^3827 ≤ 14945148884239^3827*1000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385692171 1000000000 14945148884239 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193514783/10000000000 : ℝ), (455188957/1000000000 : ℝ), (385692171/1000000000 : ℝ)] ![(6646920269961/20000000000000 : ℝ), (4609387608271/12500000000000 : ℝ), (14945148884239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193514783/10000000000 : ℝ)|^4851 ≤ (6646920269961/20000000000000 : ℝ)^3827
        have hw : |(4193514783/10000000000 : ℝ)|=(4193514783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(455188957/1000000000 : ℝ)|^4851 ≤ (4609387608271/12500000000000 : ℝ)^3827
        have hw : |(455188957/1000000000 : ℝ)|=(455188957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(385692171/1000000000 : ℝ)|^4851 ≤ (14945148884239/50000000000000 : ℝ)^3827
        have hw : |(385692171/1000000000 : ℝ)|=(385692171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1633_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8747/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1189/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2621/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4101/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8747/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1189/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8747/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1189/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8747/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1189/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8747/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1189/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8747/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1189/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8747/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1189/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1189/12500 : ℝ) ^ (4847/1024 : ℝ) ≤ (1457986596725501/100000000000000000000 : ℝ) := by
    have hpowers : (1189/12500 : ℝ)^4847 ≤ (1457986596725501/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1189 : ℕ)^4847*100000000000000000000^1024 ≤ 1457986596725501^1024*12500^4847 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1189 12500 1457986596725501 100000000000000000000 4847 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1189/12500 : ℝ)) (X := (1457986596725501/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8747/50000 : ℝ) ^ (4847/1024 : ℝ) ≤ (1629943578528197/6250000000000000000 : ℝ) := by
    have hpowers : (8747/50000 : ℝ)^4847 ≤ (1629943578528197/6250000000000000000 : ℝ)^1024 := by
      have hnat : (8747 : ℕ)^4847*6250000000000000000^1024 ≤ 1629943578528197^1024*50000^4847 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8747 50000 1629943578528197 6250000000000000000 4847 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8747/50000 : ℝ)) (X := (1629943578528197/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001457986596725501/50000000000000000000 : ℝ) ≤ (2500015400877931/2500000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (50001457986596725501/50000000000000000000 : ℝ)^1024 ≤ (2500015400877931/2500000000000000 : ℝ)^4847 := by
      have hnat : (50001457986596725501 : ℕ)^1024*2500000000000000^4847 ≤ 2500015400877931^4847*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001457986596725501 50000000000000000000 2500015400877931 2500000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500015400877931/2500000000000000 : ℝ)) (X := (50001457986596725501/50000000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027537083853176653/100000000000000000000 : ℝ) ≤ (2500145424552007/2500000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (100027537083853176653/100000000000000000000 : ℝ)^1024 ≤ (2500145424552007/2500000000000000 : ℝ)^4847 := by
      have hnat : (100027537083853176653 : ℕ)^1024*2500000000000000^4847 ≤ 2500145424552007^4847*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027537083853176653 100000000000000000000 2500145424552007 2500000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500145424552007/2500000000000000 : ℝ)) (X := (100027537083853176653/100000000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126629943578528197/3125000000000000000 : ℝ) ≤ (2500275448226083/2500000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (3126629943578528197/3125000000000000000 : ℝ)^1024 ≤ (2500275448226083/2500000000000000 : ℝ)^4847 := by
      have hnat : (3126629943578528197 : ℕ)^1024*2500000000000000^4847 ≤ 2500275448226083^4847*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126629943578528197 3125000000000000000 2500275448226083 2500000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500275448226083/2500000000000000 : ℝ)) (X := (3126629943578528197/3125000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1457986596725501/100000000000000000000 : ℝ) ≤ ((9976324679716011709/9977500000000000000 : ℝ)+2*(32505918519/49887500000000 : ℝ)*(1189/12500 : ℝ))^(4847/1024 : ℝ) := by
    rw [show (9976324679716011709/9977500000000000000 : ℝ)+2*(32505918519/49887500000000 : ℝ)*(1189/12500 : ℝ)=(2500015400877931/2500000000000000 : ℝ) by norm_num, show 1+2*(1457986596725501/100000000000000000000 : ℝ)=(50001457986596725501/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1629943578528197/6250000000000000000 : ℝ)+(1457986596725501/100000000000000000000 : ℝ) ≤ ((9976324679716011709/9977500000000000000 : ℝ)+(32505918519/49887500000000 : ℝ)*((8747/50000 : ℝ)+(1189/12500 : ℝ)))^(4847/1024 : ℝ) := by
    rw [show (9976324679716011709/9977500000000000000 : ℝ)+(32505918519/49887500000000 : ℝ)*((8747/50000 : ℝ)+(1189/12500 : ℝ))=(2500145424552007/2500000000000000 : ℝ) by norm_num, show 1+(1629943578528197/6250000000000000000 : ℝ)+(1457986596725501/100000000000000000000 : ℝ)=(100027537083853176653/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1629943578528197/6250000000000000000 : ℝ) ≤ ((9976324679716011709/9977500000000000000 : ℝ)+2*(32505918519/49887500000000 : ℝ)*(8747/50000 : ℝ))^(4847/1024 : ℝ) := by
    rw [show (9976324679716011709/9977500000000000000 : ℝ)+2*(32505918519/49887500000000 : ℝ)*(8747/50000 : ℝ)=(2500275448226083/2500000000000000 : ℝ) by norm_num, show 1+2*(1629943578528197/6250000000000000000 : ℝ)=(3126629943578528197/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9976324679716011709/9977500000000000000 : ℝ)*(X 1 0+X 2 0)+(32505918519/49887500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (1189/12500 : ℝ)) (hi := (8747/50000 : ℝ)) (c := (9976324679716011709/9977500000000000000 : ℝ)) (alpha := (32505918519/49887500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9976324679716011709/9977500000000000000 : ℝ)*(X 0 1+X 2 1)+(32505918519/49887500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (1189/12500 : ℝ)) (hi := (8747/50000 : ℝ)) (c := (9976324679716011709/9977500000000000000 : ℝ)) (alpha := (32505918519/49887500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9976324679716011709/9977500000000000000 : ℝ)*(X 0 2+X 1 2)+(32505918519/49887500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (1189/12500 : ℝ)) (hi := (8747/50000 : ℝ)) (c := (9976324679716011709/9977500000000000000 : ℝ)) (alpha := (32505918519/49887500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-823546683/5000000000 : ℝ)*X 0 0+(5457376337/10000000000 : ℝ)*X 0 1+(5178543899/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675779001/5000000000 : ℝ)*X 1 0+(-895436367/5000000000 : ℝ)*X 1 1+(1294635983/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070311601/2000000000 : ℝ)*X 2 0+(5178543901/10000000000 : ℝ)*X 2 1+(-1790872769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1048332147/2500000000 : ℝ)*X 0 0+(770276903/2000000000 : ℝ)*X 0 1+(2278683459/5000000000 : ℝ)*X 0 2+(1048332147/2500000000 : ℝ)*X 1 0+(770276903/2000000000 : ℝ)*X 1 1+(2278683459/5000000000 : ℝ)*X 1 2+(1048332147/2500000000 : ℝ)*X 2 0+(770276903/2000000000 : ℝ)*X 2 1+(2278683459/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-411791659/2500000000 : ℝ)*X 0 0+(5180707951/10000000000 : ℝ)*X 0 1+(5455189027/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((659653197/1250000000 : ℝ)*X 1 0+(-151422747/1000000000 : ℝ)*X 1 1+(5455189143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277226469/10000000000 : ℝ)*X 2 0+(5455188133/10000000000 : ℝ)*X 2 1+(-302845529/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4193514783/10000000000 : ℝ)*X 0 0+(455188957/1000000000 : ℝ)*X 0 1+(385692171/1000000000 : ℝ)*X 0 2+(4193514783/10000000000 : ℝ)*X 1 0+(455188957/1000000000 : ℝ)*X 1 1+(385692171/1000000000 : ℝ)*X 1 2+(4193514783/10000000000 : ℝ)*X 2 0+(455188957/1000000000 : ℝ)*X 2 1+(385692171/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (500628719878522047029386383/62359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (244140603/20000000000000 : ℝ)*(base19) + (224746091/20000000000000 : ℝ)*(base23) + (6621419/12500000000000 : ℝ)*(lower2) + (52457769/25000000000000 : ℝ)*(upper3) + (109531549/100000000000000 : ℝ)*(upper5) + (312680659791121/12500000000000 : ℝ)*(major0) + (312680659791121/12500000000000 : ℝ)*(major1) + (312680659791121/12500000000000 : ℝ)*(major2) + (1793199361049323/50000000000000 : ℝ)*(sp0) + (358641161914589/10000000000000 : ℝ)*(sp1) + (71728234322369/2000000000000 : ℝ)*(sp2) + (283294225386339/20000000000000 : ℝ)*(sp3) + (14117750259/100000000000000 : ℝ)*(sp4) + (6322273237/100000000000000 : ℝ)*(sp7) + (354119362301233/25000000000000 : ℝ)*(f.failure) + (448301604981113/12500000000000 : ℝ)*(f.sum) + (16933721260331/19955000000000000000000000000 : ℝ)*base65 + (134664390590151711/124718750000000000000000000000000 : ℝ)*base68 + (44915643035129539/124718750000000000000000000000000 : ℝ)*base69 + (233015225313120461/124718750000000000000000000000000 : ℝ)*base72 + (53801958233889/19955000000000000000000000000 : ℝ)*base74 + (651102305678785789/124718750000000000000000000000000 : ℝ)*base75 + (441615872944067039/124718750000000000000000000000000 : ℝ)*base77 + (370780239533317039/124718750000000000000000000000000 : ℝ)*base79 + (31744810668757/9977500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1678313/500000000000000000000 : ℝ)*base90 + (1678313/500000000000000000000 : ℝ)*base92 + (1678313/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (296278933542689498269004457/38375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (848072641/100000000000000 : ℝ)*(base19) + (1809072267/100000000000000 : ℝ)*(base23) + (127403663/100000000000000 : ℝ)*(upper3) + (74681259/50000000000000 : ℝ)*(lower4) + (2541077957803717/100000000000000 : ℝ)*(major0) + (2541077957803717/100000000000000 : ℝ)*(major1) + (2541077957803717/100000000000000 : ℝ)*(major2) + (5427363881/50000000000000 : ℝ)*(sp1) + (3043760691/20000000000000 : ℝ)*(sp2) + (323255457/20000000000000 : ℝ)*(sp3) + (1821617832323291/50000000000000 : ℝ)*(sp4) + (182161198092309/5000000000000 : ℝ)*(sp5) + (182160931838543/5000000000000 : ℝ)*(sp6) + (1438918377329439/100000000000000 : ℝ)*(sp7) + (359729998401681/25000000000000 : ℝ)*(f.failure) + (1821617832323291/50000000000000 : ℝ)*(f.sum) + (42030256921591/19955000000000000000000000000 : ℝ)*base66 + (5043679391916072353/997750000000000000000000000000000 : ℝ)*base67 + (2047767846896822353/997750000000000000000000000000000 : ℝ)*base69 + (4151789180757427647/997750000000000000000000000000000 : ℝ)*base72 + (9559579339651/19955000000000000000000000000 : ℝ)*base74 + (4766473744630677647/997750000000000000000000000000000 : ℝ)*base76 + (4159219469417322353/997750000000000000000000000000000 : ℝ)*base77 + (6692153108835322353/997750000000000000000000000000000 : ℝ)*base79 + (137390304166391/19955000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4240759/500000000000000000000 : ℝ)*base89 + (4240759/500000000000000000000 : ℝ)*base91 + (4240759/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1633_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8747/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1189/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2621/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4101/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1633_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1633_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2621/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4101/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1633_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1633_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1633_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2621/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4101/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1633_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
