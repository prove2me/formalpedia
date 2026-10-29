-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1455_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:00:26.301917+00:00
-- url     : https://prove2.me/submissions/46a701b5-1916-497d-a0a2-759adbb20090

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
theorem support_rectangle_w1455_s0_0 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1744186663/10000000000 : ℝ)*x 0 + (5949525161/10000000000 : ℝ)*x 1 + (4837146387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1744186663/10000000000 : ℝ)^4415 ≤ (5146860288723/50000000000000 : ℝ)^3391 := by
    have hnat : (1744186663 : ℕ)^4415*50000000000000^3391 ≤ 5146860288723^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744186663 10000000000 5146860288723 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5949525161/10000000000 : ℝ)^4415 ≤ (25430296250693/50000000000000 : ℝ)^3391 := by
    have hnat : (5949525161 : ℕ)^4415*50000000000000^3391 ≤ 25430296250693^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5949525161 10000000000 25430296250693 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4837146387/10000000000 : ℝ)^4415 ≤ (38845686910069/100000000000000 : ℝ)^3391 := by
    have hnat : (4837146387 : ℕ)^4415*100000000000000^3391 ≤ 38845686910069^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4837146387 10000000000 38845686910069 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1744186663/10000000000 : ℝ), (5949525161/10000000000 : ℝ), (4837146387/10000000000 : ℝ)] ![(5146860288723/50000000000000 : ℝ), (25430296250693/50000000000000 : ℝ), (38845686910069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1744186663/10000000000 : ℝ)|^4415 ≤ (5146860288723/50000000000000 : ℝ)^3391
        have hw : |(-1744186663/10000000000 : ℝ)|=(1744186663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5949525161/10000000000 : ℝ)|^4415 ≤ (25430296250693/50000000000000 : ℝ)^3391
        have hw : |(5949525161/10000000000 : ℝ)|=(5949525161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4837146387/10000000000 : ℝ)|^4415 ≤ (38845686910069/100000000000000 : ℝ)^3391
        have hw : |(4837146387/10000000000 : ℝ)|=(4837146387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s0_1 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1097842409/2000000000 : ℝ)*x 0 + (-2371442721/10000000000 : ℝ)*x 1 + (483714629/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097842409/2000000000 : ℝ)^4415 ≤ (5724773941571/12500000000000 : ℝ)^3391 := by
    have hnat : (1097842409 : ℕ)^4415*12500000000000^3391 ≤ 5724773941571^3391*2000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097842409 2000000000 5724773941571 12500000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2371442721/10000000000 : ℝ)^4415 ≤ (1919515319907/12500000000000 : ℝ)^3391 := by
    have hnat : (2371442721 : ℕ)^4415*12500000000000^3391 ≤ 1919515319907^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2371442721 10000000000 1919515319907 12500000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (483714629/1000000000 : ℝ)^4415 ≤ (19422842947929/50000000000000 : ℝ)^3391 := by
    have hnat : (483714629 : ℕ)^4415*50000000000000^3391 ≤ 19422842947929^3391*1000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483714629 1000000000 19422842947929 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1097842409/2000000000 : ℝ), (-2371442721/10000000000 : ℝ), (483714629/1000000000 : ℝ)] ![(5724773941571/12500000000000 : ℝ), (1919515319907/12500000000000 : ℝ), (19422842947929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1097842409/2000000000 : ℝ)|^4415 ≤ (5724773941571/12500000000000 : ℝ)^3391
        have hw : |(1097842409/2000000000 : ℝ)|=(1097842409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2371442721/10000000000 : ℝ)|^4415 ≤ (1919515319907/12500000000000 : ℝ)^3391
        have hw : |(-2371442721/10000000000 : ℝ)|=(2371442721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(483714629/1000000000 : ℝ)|^4415 ≤ (19422842947929/50000000000000 : ℝ)^3391
        have hw : |(483714629/1000000000 : ℝ)|=(483714629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s0_2 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2744605873/5000000000 : ℝ)*x 0 + (2418573141/5000000000 : ℝ)*x 1 + (-592860779/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2744605873/5000000000 : ℝ)^4415 ≤ (9159637656919/20000000000000 : ℝ)^3391 := by
    have hnat : (2744605873 : ℕ)^4415*20000000000000^3391 ≤ 9159637656919^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744605873 5000000000 9159637656919 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2418573141/5000000000 : ℝ)^4415 ≤ (9711421453053/25000000000000 : ℝ)^3391 := by
    have hnat : (2418573141 : ℕ)^4415*25000000000000^3391 ≤ 9711421453053^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418573141 5000000000 9711421453053 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (592860779/2500000000 : ℝ)^4415 ≤ (3071225177889/20000000000000 : ℝ)^3391 := by
    have hnat : (592860779 : ℕ)^4415*20000000000000^3391 ≤ 3071225177889^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592860779 2500000000 3071225177889 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2744605873/5000000000 : ℝ), (2418573141/5000000000 : ℝ), (-592860779/2500000000 : ℝ)] ![(9159637656919/20000000000000 : ℝ), (9711421453053/25000000000000 : ℝ), (3071225177889/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2744605873/5000000000 : ℝ)|^4415 ≤ (9159637656919/20000000000000 : ℝ)^3391
        have hw : |(2744605873/5000000000 : ℝ)|=(2744605873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2418573141/5000000000 : ℝ)|^4415 ≤ (9711421453053/25000000000000 : ℝ)^3391
        have hw : |(2418573141/5000000000 : ℝ)|=(2418573141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-592860779/2500000000 : ℝ)|^4415 ≤ (3071225177889/20000000000000 : ℝ)^3391
        have hw : |(-592860779/2500000000 : ℝ)|=(592860779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s0_3 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4162294637/10000000000 : ℝ)*x 0 + (1551402579/5000000000 : ℝ)*x 1 + (110643923/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4162294637/10000000000 : ℝ)^4415 ≤ (31943355593127/100000000000000 : ℝ)^3391 := by
    have hnat : (4162294637 : ℕ)^4415*100000000000000^3391 ≤ 31943355593127^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162294637 10000000000 31943355593127 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1551402579/5000000000 : ℝ)^4415 ≤ (21790974645233/100000000000000 : ℝ)^3391 := by
    have hnat : (1551402579 : ℕ)^4415*100000000000000^3391 ≤ 21790974645233^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551402579 5000000000 21790974645233 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110643923/200000000 : ℝ)^4415 ≤ (9253133948909/20000000000000 : ℝ)^3391 := by
    have hnat : (110643923 : ℕ)^4415*20000000000000^3391 ≤ 9253133948909^3391*200000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110643923 200000000 9253133948909 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4162294637/10000000000 : ℝ), (1551402579/5000000000 : ℝ), (110643923/200000000 : ℝ)] ![(31943355593127/100000000000000 : ℝ), (21790974645233/100000000000000 : ℝ), (9253133948909/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4162294637/10000000000 : ℝ)|^4415 ≤ (31943355593127/100000000000000 : ℝ)^3391
        have hw : |(4162294637/10000000000 : ℝ)|=(4162294637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1551402579/5000000000 : ℝ)|^4415 ≤ (21790974645233/100000000000000 : ℝ)^3391
        have hw : |(1551402579/5000000000 : ℝ)|=(1551402579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110643923/200000000 : ℝ)|^4415 ≤ (9253133948909/20000000000000 : ℝ)^3391
        have hw : |(110643923/200000000 : ℝ)|=(110643923/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s0_4 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1748081067/10000000000 : ℝ)*x 0 + (4865548887/10000000000 : ℝ)*x 1 + (370006783/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1748081067/10000000000 : ℝ)^4415 ≤ (5161827457279/50000000000000 : ℝ)^3391 := by
    have hnat : (1748081067 : ℕ)^4415*50000000000000^3391 ≤ 5161827457279^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748081067 10000000000 5161827457279 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4865548887/10000000000 : ℝ)^4415 ≤ (9785730041011/25000000000000 : ℝ)^3391 := by
    have hnat : (4865548887 : ℕ)^4415*25000000000000^3391 ≤ 9785730041011^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4865548887 10000000000 9785730041011 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (370006783/625000000 : ℝ)^4415 ≤ (50533424909831/100000000000000 : ℝ)^3391 := by
    have hnat : (370006783 : ℕ)^4415*100000000000000^3391 ≤ 50533424909831^3391*625000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370006783 625000000 50533424909831 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1748081067/10000000000 : ℝ), (4865548887/10000000000 : ℝ), (370006783/625000000 : ℝ)] ![(5161827457279/50000000000000 : ℝ), (9785730041011/25000000000000 : ℝ), (50533424909831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1748081067/10000000000 : ℝ)|^4415 ≤ (5161827457279/50000000000000 : ℝ)^3391
        have hw : |(-1748081067/10000000000 : ℝ)|=(1748081067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4865548887/10000000000 : ℝ)|^4415 ≤ (9785730041011/25000000000000 : ℝ)^3391
        have hw : |(4865548887/10000000000 : ℝ)|=(4865548887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(370006783/625000000 : ℝ)|^4415 ≤ (50533424909831/100000000000000 : ℝ)^3391
        have hw : |(370006783/625000000 : ℝ)|=(370006783/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s0_5 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324093047/625000000 : ℝ)*x 0 + (-1288480851/10000000000 : ℝ)*x 1 + (2960054299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324093047/625000000 : ℝ)^4415 ≤ (21263418460447/50000000000000 : ℝ)^3391 := by
    have hnat : (324093047 : ℕ)^4415*50000000000000^3391 ≤ 21263418460447^3391*625000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324093047 625000000 21263418460447 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1288480851/10000000000 : ℝ)^4415 ≤ (6939737365597/100000000000000 : ℝ)^3391 := by
    have hnat : (1288480851 : ℕ)^4415*100000000000000^3391 ≤ 6939737365597^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288480851 10000000000 6939737365597 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2960054299/5000000000 : ℝ)^4415 ≤ (25266712843889/50000000000000 : ℝ)^3391 := by
    have hnat : (2960054299 : ℕ)^4415*50000000000000^3391 ≤ 25266712843889^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2960054299 5000000000 25266712843889 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324093047/625000000 : ℝ), (-1288480851/10000000000 : ℝ), (2960054299/5000000000 : ℝ)] ![(21263418460447/50000000000000 : ℝ), (6939737365597/100000000000000 : ℝ), (25266712843889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324093047/625000000 : ℝ)|^4415 ≤ (21263418460447/50000000000000 : ℝ)^3391
        have hw : |(324093047/625000000 : ℝ)|=(324093047/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1288480851/10000000000 : ℝ)|^4415 ≤ (6939737365597/100000000000000 : ℝ)^3391
        have hw : |(-1288480851/10000000000 : ℝ)|=(1288480851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2960054299/5000000000 : ℝ)|^4415 ≤ (25266712843889/50000000000000 : ℝ)^3391
        have hw : |(2960054299/5000000000 : ℝ)|=(2960054299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s0_6 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2592744393/5000000000 : ℝ)*x 0 + (5920108441/10000000000 : ℝ)*x 1 + (-25769621/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592744393/5000000000 : ℝ)^4415 ≤ (21263418641967/50000000000000 : ℝ)^3391 := by
    have hnat : (2592744393 : ℕ)^4415*50000000000000^3391 ≤ 21263418641967^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592744393 5000000000 21263418641967 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5920108441/10000000000 : ℝ)^4415 ≤ (25266711971477/50000000000000 : ℝ)^3391 := by
    have hnat : (5920108441 : ℕ)^4415*50000000000000^3391 ≤ 25266711971477^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5920108441 10000000000 25266711971477 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25769621/200000000 : ℝ)^4415 ≤ (6939738761069/100000000000000 : ℝ)^3391 := by
    have hnat : (25769621 : ℕ)^4415*100000000000000^3391 ≤ 6939738761069^3391*200000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25769621 200000000 6939738761069 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2592744393/5000000000 : ℝ), (5920108441/10000000000 : ℝ), (-25769621/200000000 : ℝ)] ![(21263418641967/50000000000000 : ℝ), (25266711971477/50000000000000 : ℝ), (6939738761069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2592744393/5000000000 : ℝ)|^4415 ≤ (21263418641967/50000000000000 : ℝ)^3391
        have hw : |(2592744393/5000000000 : ℝ)|=(2592744393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5920108441/10000000000 : ℝ)|^4415 ≤ (25266711971477/50000000000000 : ℝ)^3391
        have hw : |(5920108441/10000000000 : ℝ)|=(5920108441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25769621/200000000 : ℝ)|^4415 ≤ (6939738761069/100000000000000 : ℝ)^3391
        have hw : |(-25769621/200000000 : ℝ)|=(25769621/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s0_7 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4170798561/10000000000 : ℝ)*x 0 + (5470165603/10000000000 : ℝ)*x 1 + (3167050287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4170798561/10000000000 : ℝ)^4415 ≤ (32028352650863/100000000000000 : ℝ)^3391 := by
    have hnat : (4170798561 : ℕ)^4415*100000000000000^3391 ≤ 32028352650863^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170798561 10000000000 32028352650863 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470165603/10000000000 : ℝ)^4415 ≤ (1823656103289/4000000000000 : ℝ)^3391 := by
    have hnat : (5470165603 : ℕ)^4415*4000000000000^3391 ≤ 1823656103289^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470165603 10000000000 1823656103289 4000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3167050287/10000000000 : ℝ)^4415 ≤ (22380244763227/100000000000000 : ℝ)^3391 := by
    have hnat : (3167050287 : ℕ)^4415*100000000000000^3391 ≤ 22380244763227^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3167050287 10000000000 22380244763227 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4170798561/10000000000 : ℝ), (5470165603/10000000000 : ℝ), (3167050287/10000000000 : ℝ)] ![(32028352650863/100000000000000 : ℝ), (1823656103289/4000000000000 : ℝ), (22380244763227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4170798561/10000000000 : ℝ)|^4415 ≤ (32028352650863/100000000000000 : ℝ)^3391
        have hw : |(4170798561/10000000000 : ℝ)|=(4170798561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470165603/10000000000 : ℝ)|^4415 ≤ (1823656103289/4000000000000 : ℝ)^3391
        have hw : |(5470165603/10000000000 : ℝ)|=(5470165603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3167050287/10000000000 : ℝ)|^4415 ≤ (22380244763227/100000000000000 : ℝ)^3391
        have hw : |(3167050287/10000000000 : ℝ)|=(3167050287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1455_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (223/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (163/625 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2207/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2207 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2207*1^512 ≤ 0^512*1^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2207/512 : ℝ) ≤ (385204130036602547/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2207 ≤ (385204130036602547/20000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2207*20000000000000000000^512 ≤ 385204130036602547^512*5^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 385204130036602547 20000000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (385204130036602547/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2207 := by
      have hnat : (1 : ℕ)^512*1^2207 ≤ 1^2207*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20385204130036602547/20000000000000000000 : ℝ) ≤ (39235761016877/39062500000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (20385204130036602547/20000000000000000000 : ℝ)^512 ≤ (39235761016877/39062500000000 : ℝ)^2207 := by
      have hnat : (20385204130036602547 : ℕ)^512*39062500000000^2207 ≤ 39235761016877^2207*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20385204130036602547 20000000000000000000 39235761016877 39062500000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39235761016877/39062500000000 : ℝ)) (X := (20385204130036602547/20000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10385204130036602547/10000000000000000000 : ℝ) ≤ (19704511016877/19531250000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (10385204130036602547/10000000000000000000 : ℝ)^512 ≤ (19704511016877/19531250000000 : ℝ)^2207 := by
      have hnat : (10385204130036602547 : ℕ)^512*19531250000000^2207 ≤ 19704511016877^2207*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10385204130036602547 10000000000000000000 19704511016877 19531250000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (19704511016877/19531250000000 : ℝ)) (X := (10385204130036602547/10000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(173261016877/15625000000000 : ℝ)*(0 : ℝ))^(2207/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(173261016877/15625000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(385204130036602547/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(173261016877/15625000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2207/512 : ℝ) := by
    rw [show (1 : ℝ)+(173261016877/15625000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(39235761016877/39062500000000 : ℝ) by norm_num, show 1+(385204130036602547/20000000000000000000 : ℝ)+(0 : ℝ)=(20385204130036602547/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(385204130036602547/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(173261016877/15625000000000 : ℝ)*(2/5 : ℝ))^(2207/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(173261016877/15625000000000 : ℝ)*(2/5 : ℝ)=(19704511016877/19531250000000 : ℝ) by norm_num, show 1+2*(385204130036602547/20000000000000000000 : ℝ)=(10385204130036602547/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(173261016877/15625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (173261016877/15625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(173261016877/15625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (173261016877/15625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(173261016877/15625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (173261016877/15625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1744186663/10000000000 : ℝ)*X 0 0+(5949525161/10000000000 : ℝ)*X 0 1+(4837146387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1097842409/2000000000 : ℝ)*X 1 0+(-2371442721/10000000000 : ℝ)*X 1 1+(483714629/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2744605873/5000000000 : ℝ)*X 2 0+(2418573141/5000000000 : ℝ)*X 2 1+(-592860779/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4162294637/10000000000 : ℝ)*X 0 0+(1551402579/5000000000 : ℝ)*X 0 1+(110643923/200000000 : ℝ)*X 0 2+(4162294637/10000000000 : ℝ)*X 1 0+(1551402579/5000000000 : ℝ)*X 1 1+(110643923/200000000 : ℝ)*X 1 2+(4162294637/10000000000 : ℝ)*X 2 0+(1551402579/5000000000 : ℝ)*X 2 1+(110643923/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1748081067/10000000000 : ℝ)*X 0 0+(4865548887/10000000000 : ℝ)*X 0 1+(370006783/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((324093047/625000000 : ℝ)*X 1 0+(-1288480851/10000000000 : ℝ)*X 1 1+(2960054299/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2592744393/5000000000 : ℝ)*X 2 0+(5920108441/10000000000 : ℝ)*X 2 1+(-25769621/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4170798561/10000000000 : ℝ)*X 0 0+(5470165603/10000000000 : ℝ)*X 0 1+(3167050287/10000000000 : ℝ)*X 0 2+(4170798561/10000000000 : ℝ)*X 1 0+(5470165603/10000000000 : ℝ)*X 1 1+(3167050287/10000000000 : ℝ)*X 1 2+(4170798561/10000000000 : ℝ)*X 2 0+(5470165603/10000000000 : ℝ)*X 2 1+(3167050287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6594464493240876684891/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (146438397/100000000000000 : ℝ)*(base1) + (18569221/100000000000000 : ℝ)*(base16) + (452445801/100000000000000 : ℝ)*(base19) + (422047381/100000000000000 : ℝ)*(base23) + (59973257/100000000000000 : ℝ)*(upper3) + (655301555478583/100000000000000 : ℝ)*(major0) + (655301555478583/100000000000000 : ℝ)*(major1) + (655301555478583/100000000000000 : ℝ)*(major2) + (449487790171753/50000000000000 : ℝ)*(sp0) + (898975748524399/100000000000000 : ℝ)*(sp1) + (22474394937301/2500000000000 : ℝ)*(sp2) + (803957337927/195312500000 : ℝ)*(sp3) + (98204289/12500000000000 : ℝ)*(sp4) + (517619767/100000000000000 : ℝ)*(sp7) + (102906705269197/25000000000000 : ℝ)*(f.failure) + (898976219539421/100000000000000 : ℝ)*(f.sum) + (1692485421961/3125000000000000000000000000 : ℝ)*base66 + (5629130393707/3125000000000000000000000000 : ℝ)*base67 + (12514617943707/3125000000000000000000000000 : ℝ)*base69 + (1200908827333/781250000000000000000000000 : ℝ)*base71 + (6173811493793/1562500000000000000000000000 : ℝ)*base74 + (9483667468707/3125000000000000000000000000 : ℝ)*base75 + (608898168707/3125000000000000000000000000 : ℝ)*base77 + (12191536424957/3125000000000000000000000000 : ℝ)*base79 + (7476012403039/3125000000000000000000000000 : ℝ)*base81 + (6737681/2500000000000000000000 : ℝ)*base89 + (6737681/2500000000000000000000 : ℝ)*base91 + (6737681/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22646964453825103856079/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (206963347/12500000000000 : ℝ)*(base19) + (1670682149/100000000000000 : ℝ)*(base23) + (153661577/100000000000000 : ℝ)*(base32) + (249561039/100000000000000 : ℝ)*(upper3) + (38179677/25000000000000 : ℝ)*(upper5) + (691228463595071/100000000000000 : ℝ)*(major0) + (691228463595071/100000000000000 : ℝ)*(major1) + (691228463595071/100000000000000 : ℝ)*(major2) + (1997240249/50000000000000 : ℝ)*(sp1) + (4144008511/100000000000000 : ℝ)*(sp2) + (474131211934137/50000000000000 : ℝ)*(sp4) + (948256773681/100000000000 : ℝ)*(sp5) + (474128304588807/50000000000000 : ℝ)*(sp6) + (434194108092667/100000000000000 : ℝ)*(sp7) + (108548565438561/25000000000000 : ℝ)*(f.failure) + (474131211934137/50000000000000 : ℝ)*(f.sum) + (1796261912557/3125000000000000000000000000 : ℝ)*base66 + (1231888220341/3125000000000000000000000000 : ℝ)*base68 + (1062331539091/3125000000000000000000000000 : ℝ)*base70 + (15289133089091/3125000000000000000000000000 : ℝ)*base72 + (13135102731193/3125000000000000000000000000 : ℝ)*base73 + (847487001591/3125000000000000000000000000 : ℝ)*base76 + (8755059339091/3125000000000000000000000000 : ℝ)*base78 + (410815410909/3125000000000000000000000000 : ℝ)*base79 + (7677217387443/3125000000000000000000000000 : ℝ)*base81 + (7763147/2500000000000000000000 : ℝ)*base90 + (7763147/2500000000000000000000 : ℝ)*base92 + (7763147/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1455_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (223/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (163/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1455_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1455_s1_0 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1912869137/10000000000 : ℝ)*x 0 + (5594985669/10000000000 : ℝ)*x 1 + (1016700397/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1912869137/10000000000 : ℝ)^4415 ≤ (2902094749127/25000000000000 : ℝ)^3391 := by
    have hnat : (1912869137 : ℕ)^4415*25000000000000^3391 ≤ 2902094749127^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912869137 10000000000 2902094749127 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5594985669/10000000000 : ℝ)^4415 ≤ (2347525794301/5000000000000 : ℝ)^3391 := by
    have hnat : (5594985669 : ℕ)^4415*5000000000000^3391 ≤ 2347525794301^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5594985669 10000000000 2347525794301 5000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016700397/2000000000 : ℝ)^4415 ≤ (20720552552913/50000000000000 : ℝ)^3391 := by
    have hnat : (1016700397 : ℕ)^4415*50000000000000^3391 ≤ 20720552552913^3391*2000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016700397 2000000000 20720552552913 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1912869137/10000000000 : ℝ), (5594985669/10000000000 : ℝ), (1016700397/2000000000 : ℝ)] ![(2902094749127/25000000000000 : ℝ), (2347525794301/5000000000000 : ℝ), (20720552552913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1912869137/10000000000 : ℝ)|^4415 ≤ (2902094749127/25000000000000 : ℝ)^3391
        have hw : |(-1912869137/10000000000 : ℝ)|=(1912869137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5594985669/10000000000 : ℝ)|^4415 ≤ (2347525794301/5000000000000 : ℝ)^3391
        have hw : |(5594985669/10000000000 : ℝ)|=(5594985669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016700397/2000000000 : ℝ)|^4415 ≤ (20720552552913/50000000000000 : ℝ)^3391
        have hw : |(1016700397/2000000000 : ℝ)|=(1016700397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s1_1 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337138711/625000000 : ℝ)*x 0 + (-1091685249/5000000000 : ℝ)*x 1 + (2541751923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337138711/625000000 : ℝ)^4415 ≤ (44769013606533/100000000000000 : ℝ)^3391 := by
    have hnat : (337138711 : ℕ)^4415*100000000000000^3391 ≤ 44769013606533^3391*625000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337138711 625000000 44769013606533 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091685249/5000000000 : ℝ)^4415 ≤ (861866345037/6250000000000 : ℝ)^3391 := by
    have hnat : (1091685249 : ℕ)^4415*6250000000000^3391 ≤ 861866345037^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091685249 5000000000 861866345037 6250000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541751923/5000000000 : ℝ)^4415 ≤ (66305799773/160000000000 : ℝ)^3391 := by
    have hnat : (2541751923 : ℕ)^4415*160000000000^3391 ≤ 66305799773^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541751923 5000000000 66305799773 160000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337138711/625000000 : ℝ), (-1091685249/5000000000 : ℝ), (2541751923/5000000000 : ℝ)] ![(44769013606533/100000000000000 : ℝ), (861866345037/6250000000000 : ℝ), (66305799773/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337138711/625000000 : ℝ)|^4415 ≤ (44769013606533/100000000000000 : ℝ)^3391
        have hw : |(337138711/625000000 : ℝ)|=(337138711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091685249/5000000000 : ℝ)|^4415 ≤ (861866345037/6250000000000 : ℝ)^3391
        have hw : |(-1091685249/5000000000 : ℝ)|=(1091685249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541751923/5000000000 : ℝ)|^4415 ≤ (66305799773/160000000000 : ℝ)^3391
        have hw : |(2541751923/5000000000 : ℝ)|=(2541751923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s1_2 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394220929/10000000000 : ℝ)*x 0 + (1270875529/2500000000 : ℝ)*x 1 + (-2183370691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394220929/10000000000 : ℝ)^4415 ≤ (8953806077549/20000000000000 : ℝ)^3391 := by
    have hnat : (5394220929 : ℕ)^4415*20000000000000^3391 ≤ 8953806077549^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394220929 10000000000 8953806077549 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270875529/2500000000 : ℝ)^4415 ≤ (8288221299247/20000000000000 : ℝ)^3391 := by
    have hnat : (1270875529 : ℕ)^4415*20000000000000^3391 ≤ 8288221299247^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270875529 2500000000 8288221299247 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2183370691/10000000000 : ℝ)^4415 ≤ (275797262153/2000000000000 : ℝ)^3391 := by
    have hnat : (2183370691 : ℕ)^4415*2000000000000^3391 ≤ 275797262153^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183370691 10000000000 275797262153 2000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394220929/10000000000 : ℝ), (1270875529/2500000000 : ℝ), (-2183370691/10000000000 : ℝ)] ![(8953806077549/20000000000000 : ℝ), (8288221299247/20000000000000 : ℝ), (275797262153/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394220929/10000000000 : ℝ)|^4415 ≤ (8953806077549/20000000000000 : ℝ)^3391
        have hw : |(5394220929/10000000000 : ℝ)|=(5394220929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270875529/2500000000 : ℝ)|^4415 ≤ (8288221299247/20000000000000 : ℝ)^3391
        have hw : |(1270875529/2500000000 : ℝ)|=(1270875529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2183370691/10000000000 : ℝ)|^4415 ≤ (275797262153/2000000000000 : ℝ)^3391
        have hw : |(-2183370691/10000000000 : ℝ)|=(2183370691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s1_3 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4271902423/10000000000 : ℝ)*x 0 + (468201699/1250000000 : ℝ)*x 1 + (2431334631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4271902423/10000000000 : ℝ)^4415 ≤ (6608576046731/20000000000000 : ℝ)^3391 := by
    have hnat : (4271902423 : ℕ)^4415*20000000000000^3391 ≤ 6608576046731^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271902423 10000000000 6608576046731 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468201699/1250000000 : ℝ)^4415 ≤ (3480544861763/12500000000000 : ℝ)^3391 := by
    have hnat : (468201699 : ℕ)^4415*12500000000000^3391 ≤ 3480544861763^3391*1250000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468201699 1250000000 3480544861763 12500000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2431334631/5000000000 : ℝ)^4415 ≤ (9778190213203/25000000000000 : ℝ)^3391 := by
    have hnat : (2431334631 : ℕ)^4415*25000000000000^3391 ≤ 9778190213203^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431334631 5000000000 9778190213203 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4271902423/10000000000 : ℝ), (468201699/1250000000 : ℝ), (2431334631/5000000000 : ℝ)] ![(6608576046731/20000000000000 : ℝ), (3480544861763/12500000000000 : ℝ), (9778190213203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4271902423/10000000000 : ℝ)|^4415 ≤ (6608576046731/20000000000000 : ℝ)^3391
        have hw : |(4271902423/10000000000 : ℝ)|=(4271902423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(468201699/1250000000 : ℝ)|^4415 ≤ (3480544861763/12500000000000 : ℝ)^3391
        have hw : |(468201699/1250000000 : ℝ)|=(468201699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2431334631/5000000000 : ℝ)|^4415 ≤ (9778190213203/25000000000000 : ℝ)^3391
        have hw : |(2431334631/5000000000 : ℝ)|=(2431334631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s1_4 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1913233227/10000000000 : ℝ)*x 0 + (2544689287/5000000000 : ℝ)*x 1 + (2794505751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1913233227/10000000000 : ℝ)^4415 ≤ (11611255801793/100000000000000 : ℝ)^3391 := by
    have hnat : (1913233227 : ℕ)^4415*100000000000000^3391 ≤ 11611255801793^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913233227 10000000000 11611255801793 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2544689287/5000000000 : ℝ)^4415 ≤ (20751744490089/50000000000000 : ℝ)^3391 := by
    have hnat : (2544689287 : ℕ)^4415*50000000000000^3391 ≤ 20751744490089^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544689287 5000000000 20751744490089 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2794505751/5000000000 : ℝ)^4415 ≤ (23442627600617/50000000000000 : ℝ)^3391 := by
    have hnat : (2794505751 : ℕ)^4415*50000000000000^3391 ≤ 23442627600617^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794505751 5000000000 23442627600617 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1913233227/10000000000 : ℝ), (2544689287/5000000000 : ℝ), (2794505751/5000000000 : ℝ)] ![(11611255801793/100000000000000 : ℝ), (20751744490089/50000000000000 : ℝ), (23442627600617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1913233227/10000000000 : ℝ)|^4415 ≤ (11611255801793/100000000000000 : ℝ)^3391
        have hw : |(-1913233227/10000000000 : ℝ)|=(1913233227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2544689287/5000000000 : ℝ)|^4415 ≤ (20751744490089/50000000000000 : ℝ)^3391
        have hw : |(2544689287/5000000000 : ℝ)|=(2544689287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2794505751/5000000000 : ℝ)|^4415 ≤ (23442627600617/50000000000000 : ℝ)^3391
        have hw : |(2794505751/5000000000 : ℝ)|=(2794505751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s1_5 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260330079/10000000000 : ℝ)*x 0 + (-838931071/5000000000 : ℝ)*x 1 + (5589011537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260330079/10000000000 : ℝ)^4415 ≤ (676995362523/1562500000000 : ℝ)^3391 := by
    have hnat : (5260330079 : ℕ)^4415*1562500000000^3391 ≤ 676995362523^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260330079 10000000000 676995362523 1562500000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (838931071/5000000000 : ℝ)^4415 ≤ (9787041206059/100000000000000 : ℝ)^3391 := by
    have hnat : (838931071 : ℕ)^4415*100000000000000^3391 ≤ 9787041206059^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838931071 5000000000 9787041206059 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5589011537/10000000000 : ℝ)^4415 ≤ (23442627791753/50000000000000 : ℝ)^3391 := by
    have hnat : (5589011537 : ℕ)^4415*50000000000000^3391 ≤ 23442627791753^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5589011537 10000000000 23442627791753 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260330079/10000000000 : ℝ), (-838931071/5000000000 : ℝ), (5589011537/10000000000 : ℝ)] ![(676995362523/1562500000000 : ℝ), (9787041206059/100000000000000 : ℝ), (23442627791753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260330079/10000000000 : ℝ)|^4415 ≤ (676995362523/1562500000000 : ℝ)^3391
        have hw : |(5260330079/10000000000 : ℝ)|=(5260330079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-838931071/5000000000 : ℝ)|^4415 ≤ (9787041206059/100000000000000 : ℝ)^3391
        have hw : |(-838931071/5000000000 : ℝ)|=(838931071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5589011537/10000000000 : ℝ)|^4415 ≤ (23442627791753/50000000000000 : ℝ)^3391
        have hw : |(5589011537/10000000000 : ℝ)|=(5589011537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s1_6 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526032997/1000000000 : ℝ)*x 0 + (5589011499/10000000000 : ℝ)*x 1 + (-1677862349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526032997/1000000000 : ℝ)^4415 ≤ (43327702032559/100000000000000 : ℝ)^3391 := by
    have hnat : (526032997 : ℕ)^4415*100000000000000^3391 ≤ 43327702032559^3391*1000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526032997 1000000000 43327702032559 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5589011499/10000000000 : ℝ)^4415 ≤ (11721313792117/25000000000000 : ℝ)^3391 := by
    have hnat : (5589011499 : ℕ)^4415*25000000000000^3391 ≤ 11721313792117^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5589011499 10000000000 11721313792117 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1677862349/10000000000 : ℝ)^4415 ≤ (2446760694529/25000000000000 : ℝ)^3391 := by
    have hnat : (1677862349 : ℕ)^4415*25000000000000^3391 ≤ 2446760694529^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677862349 10000000000 2446760694529 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526032997/1000000000 : ℝ), (5589011499/10000000000 : ℝ), (-1677862349/10000000000 : ℝ)] ![(43327702032559/100000000000000 : ℝ), (11721313792117/25000000000000 : ℝ), (2446760694529/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526032997/1000000000 : ℝ)|^4415 ≤ (43327702032559/100000000000000 : ℝ)^3391
        have hw : |(526032997/1000000000 : ℝ)|=(526032997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5589011499/10000000000 : ℝ)|^4415 ≤ (11721313792117/25000000000000 : ℝ)^3391
        have hw : |(5589011499/10000000000 : ℝ)|=(5589011499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1677862349/10000000000 : ℝ)|^4415 ≤ (2446760694529/25000000000000 : ℝ)^3391
        have hw : |(-1677862349/10000000000 : ℝ)|=(1677862349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s1_7 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534087281/1250000000 : ℝ)*x 0 + (242491833/500000000 : ℝ)*x 1 + (3758658069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534087281/1250000000 : ℝ)^4415 ≤ (16525447485397/50000000000000 : ℝ)^3391 := by
    have hnat : (534087281 : ℕ)^4415*50000000000000^3391 ≤ 16525447485397^3391*1250000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534087281 1250000000 16525447485397 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242491833/500000000 : ℝ)^4415 ≤ (38978426157359/100000000000000 : ℝ)^3391 := by
    have hnat : (242491833 : ℕ)^4415*100000000000000^3391 ≤ 38978426157359^3391*500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242491833 500000000 38978426157359 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3758658069/10000000000 : ℝ)^4415 ≤ (43704185701/156250000000 : ℝ)^3391 := by
    have hnat : (3758658069 : ℕ)^4415*156250000000^3391 ≤ 43704185701^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3758658069 10000000000 43704185701 156250000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534087281/1250000000 : ℝ), (242491833/500000000 : ℝ), (3758658069/10000000000 : ℝ)] ![(16525447485397/50000000000000 : ℝ), (38978426157359/100000000000000 : ℝ), (43704185701/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534087281/1250000000 : ℝ)|^4415 ≤ (16525447485397/50000000000000 : ℝ)^3391
        have hw : |(534087281/1250000000 : ℝ)|=(534087281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(242491833/500000000 : ℝ)|^4415 ≤ (38978426157359/100000000000000 : ℝ)^3391
        have hw : |(242491833/500000000 : ℝ)|=(242491833/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3758658069/10000000000 : ℝ)|^4415 ≤ (43704185701/156250000000 : ℝ)^3391
        have hw : |(3758658069/10000000000 : ℝ)|=(3758658069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1455_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (163/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (3931/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18677/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (163/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (223/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (163/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (223/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (163/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (223/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (163/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (223/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (163/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (223/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (163/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (223/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (223/10000 : ℝ) ^ (2207/512 : ℝ) ≤ (7590854883217/100000000000000000000 : ℝ) := by
    have hpowers : (223/10000 : ℝ)^2207 ≤ (7590854883217/100000000000000000000 : ℝ)^512 := by
      have hnat : (223 : ℕ)^2207*100000000000000000000^512 ≤ 7590854883217^512*10000^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        223 10000 7590854883217 100000000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (223/10000 : ℝ)) (X := (7590854883217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hpowhi : (163/625 : ℝ) ^ (2207/512 : ℝ) ≤ (304765984840038159/100000000000000000000 : ℝ) := by
    have hpowers : (163/625 : ℝ)^2207 ≤ (304765984840038159/100000000000000000000 : ℝ)^512 := by
      have hnat : (163 : ℕ)^2207*100000000000000000000^512 ≤ 304765984840038159^512*625^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        163 625 304765984840038159 100000000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (163/625 : ℝ)) (X := (304765984840038159/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000007590854883217/50000000000000000000 : ℝ) ≤ (10000000352199137/10000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (50000007590854883217/50000000000000000000 : ℝ)^512 ≤ (10000000352199137/10000000000000000 : ℝ)^2207 := by
      have hnat : (50000007590854883217 : ℕ)^512*10000000000000000^2207 ≤ 10000000352199137^2207*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000007590854883217 50000000000000000000 10000000352199137 10000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000352199137/10000000000000000 : ℝ)) (X := (50000007590854883217/50000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (3134524174240466293/3125000000000000000 : ℝ) ≤ (5003531077760797/5000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (3134524174240466293/3125000000000000000 : ℝ)^512 ≤ (5003531077760797/5000000000000000 : ℝ)^2207 := by
      have hnat : (3134524174240466293 : ℕ)^512*5000000000000000^2207 ≤ 5003531077760797^2207*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3134524174240466293 3125000000000000000 5003531077760797 5000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003531077760797/5000000000000000 : ℝ)) (X := (3134524174240466293/3125000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50304765984840038159/50000000000000000000 : ℝ) ≤ (10014123958844051/10000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (50304765984840038159/50000000000000000000 : ℝ)^512 ≤ (10014123958844051/10000000000000000 : ℝ)^2207 := by
      have hnat : (50304765984840038159 : ℕ)^512*10000000000000000^2207 ≤ 10014123958844051^2207*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50304765984840038159 50000000000000000000 10014123958844051 10000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014123958844051/10000000000000000 : ℝ)) (X := (50304765984840038159/50000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7590854883217/100000000000000000000 : ℝ) ≤ ((7948950425237708641/7950000000000000000 : ℝ)+2*(2353934440819/795000000000000 : ℝ)*(223/10000 : ℝ))^(2207/512 : ℝ) := by
    rw [show (7948950425237708641/7950000000000000000 : ℝ)+2*(2353934440819/795000000000000 : ℝ)*(223/10000 : ℝ)=(10000000352199137/10000000000000000 : ℝ) by norm_num, show 1+2*(7590854883217/100000000000000000000 : ℝ)=(50000007590854883217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(304765984840038159/100000000000000000000 : ℝ)+(7590854883217/100000000000000000000 : ℝ) ≤ ((7948950425237708641/7950000000000000000 : ℝ)+(2353934440819/795000000000000 : ℝ)*((163/625 : ℝ)+(223/10000 : ℝ)))^(2207/512 : ℝ) := by
    rw [show (7948950425237708641/7950000000000000000 : ℝ)+(2353934440819/795000000000000 : ℝ)*((163/625 : ℝ)+(223/10000 : ℝ))=(5003531077760797/5000000000000000 : ℝ) by norm_num, show 1+(304765984840038159/100000000000000000000 : ℝ)+(7590854883217/100000000000000000000 : ℝ)=(3134524174240466293/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(304765984840038159/100000000000000000000 : ℝ) ≤ ((7948950425237708641/7950000000000000000 : ℝ)+2*(2353934440819/795000000000000 : ℝ)*(163/625 : ℝ))^(2207/512 : ℝ) := by
    rw [show (7948950425237708641/7950000000000000000 : ℝ)+2*(2353934440819/795000000000000 : ℝ)*(163/625 : ℝ)=(10014123958844051/10000000000000000 : ℝ) by norm_num, show 1+2*(304765984840038159/100000000000000000000 : ℝ)=(50304765984840038159/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7948950425237708641/7950000000000000000 : ℝ)*(X 1 0+X 2 0)+(2353934440819/795000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (223/10000 : ℝ)) (hi := (163/625 : ℝ)) (c := (7948950425237708641/7950000000000000000 : ℝ)) (alpha := (2353934440819/795000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7948950425237708641/7950000000000000000 : ℝ)*(X 0 1+X 2 1)+(2353934440819/795000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (223/10000 : ℝ)) (hi := (163/625 : ℝ)) (c := (7948950425237708641/7950000000000000000 : ℝ)) (alpha := (2353934440819/795000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7948950425237708641/7950000000000000000 : ℝ)*(X 0 2+X 1 2)+(2353934440819/795000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (223/10000 : ℝ)) (hi := (163/625 : ℝ)) (c := (7948950425237708641/7950000000000000000 : ℝ)) (alpha := (2353934440819/795000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1912869137/10000000000 : ℝ)*X 0 0+(5594985669/10000000000 : ℝ)*X 0 1+(1016700397/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((337138711/625000000 : ℝ)*X 1 0+(-1091685249/5000000000 : ℝ)*X 1 1+(2541751923/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5394220929/10000000000 : ℝ)*X 2 0+(1270875529/2500000000 : ℝ)*X 2 1+(-2183370691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4271902423/10000000000 : ℝ)*X 0 0+(468201699/1250000000 : ℝ)*X 0 1+(2431334631/5000000000 : ℝ)*X 0 2+(4271902423/10000000000 : ℝ)*X 1 0+(468201699/1250000000 : ℝ)*X 1 1+(2431334631/5000000000 : ℝ)*X 1 2+(4271902423/10000000000 : ℝ)*X 2 0+(468201699/1250000000 : ℝ)*X 2 1+(2431334631/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1913233227/10000000000 : ℝ)*X 0 0+(2544689287/5000000000 : ℝ)*X 0 1+(2794505751/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260330079/10000000000 : ℝ)*X 1 0+(-838931071/5000000000 : ℝ)*X 1 1+(5589011537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((526032997/1000000000 : ℝ)*X 2 0+(5589011499/10000000000 : ℝ)*X 2 1+(-1677862349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((534087281/1250000000 : ℝ)*X 0 0+(242491833/500000000 : ℝ)*X 0 1+(3758658069/10000000000 : ℝ)*X 0 2+(534087281/1250000000 : ℝ)*X 1 0+(242491833/500000000 : ℝ)*X 1 1+(3758658069/10000000000 : ℝ)*X 1 2+(534087281/1250000000 : ℝ)*X 2 0+(242491833/500000000 : ℝ)*X 2 1+(3758658069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (134784528189911412806240433/33125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (586080521/100000000000000 : ℝ)*(base19) + (264414209/25000000000000 : ℝ)*(base23) + (47311523/100000000000000 : ℝ)*(upper3) + (4925119/10000000000000 : ℝ)*(upper4) + (9011261/100000000000000 : ℝ)*(upper5) + (712584166525887/50000000000000 : ℝ)*(major0) + (712584166525887/50000000000000 : ℝ)*(major1) + (712584166525887/50000000000000 : ℝ)*(major2) + (78204277239917/4000000000000 : ℝ)*(sp0) + (391023661351363/20000000000000 : ℝ)*(sp1) + (3910235670361/200000000000 : ℝ)*(sp2) + (447606787036691/50000000000000 : ℝ)*(sp3) + (11961839411/100000000000000 : ℝ)*(sp4) + (4063560593/100000000000000 : ℝ)*(sp7) + (111902204704247/12500000000000 : ℝ)*(f.failure) + (244389861604667/12500000000000 : ℝ)*(f.sum) + (16402760791651/6625000000000000000000000000 : ℝ)*base65 + (1126666582187373189/132500000000000000000000000000000 : ℝ)*base67 + (268648674825126811/132500000000000000000000000000000 : ℝ)*base70 + (679833012609873189/132500000000000000000000000000000 : ℝ)*base71 + (28564882619401/6625000000000000000000000000 : ℝ)*base73 + (537623889477373189/132500000000000000000000000000000 : ℝ)*base75 + (361881102159873189/132500000000000000000000000000000 : ℝ)*base77 + (1818843765104873189/132500000000000000000000000000000 : ℝ)*base79 + (4211345058487/3312500000000000000000000000 : ℝ)*base82 + (11891331/1250000000000000000000 : ℝ)*base89 + (11891331/1250000000000000000000 : ℝ)*base91 + (11891331/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (260522491434150571079554413/26500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2090430519/100000000000000 : ℝ)*(base19) + (428639513/20000000000000 : ℝ)*(base23) + (2058671/800000000000 : ℝ)*(upper3) + (5872261/12500000000000 : ℝ)*(lower4) + (206554981/100000000000000 : ℝ)*(upper5) + (291790890521107/20000000000000 : ℝ)*(major0) + (291790890521107/20000000000000 : ℝ)*(major1) + (291790890521107/20000000000000 : ℝ)*(major2) + (13288774159/100000000000000 : ℝ)*(sp1) + (13482431137/100000000000000 : ℝ)*(sp2) + (1000734116376981/50000000000000 : ℝ)*(sp4) + (500363213387321/25000000000000 : ℝ)*(sp5) + (100072630356263/5000000000000 : ℝ)*(sp6) + (57277521547241/6250000000000 : ℝ)*(sp7) + (57277521547241/6250000000000 : ℝ)*(f.failure) + (1000734116376981/50000000000000 : ℝ)*(f.sum) + (29821634800333/7950000000000000000000000000 : ℝ)*base65 + (704910353261115587/159000000000000000000000000000000 : ℝ)*base67 + (491498159298884413/159000000000000000000000000000000 : ℝ)*base70 + (414883643021115587/159000000000000000000000000000000 : ℝ)*base71 + (31620969939133/7950000000000000000000000000 : ℝ)*base73 + (304185680880884413/159000000000000000000000000000000 : ℝ)*base76 + (187721892794115587/159000000000000000000000000000000 : ℝ)*base77 + (383612622665115587/159000000000000000000000000000000 : ℝ)*base79 + (26244275356517/7950000000000000000000000000 : ℝ)*base82 + (2807507/625000000000000000000 : ℝ)*base90 + (2807507/625000000000000000000 : ℝ)*base92 + (2807507/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1455_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (163/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3931/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18677/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1455_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1455_s2_0 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-388821883/2000000000 : ℝ)*x 0 + (272626223/500000000 : ℝ)*x 1 + (1301456417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (388821883/2000000000 : ℝ)^4415 ≤ (11855818875507/100000000000000 : ℝ)^3391 := by
    have hnat : (388821883 : ℕ)^4415*100000000000000^3391 ≤ 11855818875507^3391*2000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388821883 2000000000 11855818875507 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272626223/500000000 : ℝ)^4415 ≤ (11350016233137/25000000000000 : ℝ)^3391 := by
    have hnat : (272626223 : ℕ)^4415*25000000000000^3391 ≤ 11350016233137^3391*500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272626223 500000000 11350016233137 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301456417/2500000000 : ℝ)^4415 ≤ (42744116173559/100000000000000 : ℝ)^3391 := by
    have hnat : (1301456417 : ℕ)^4415*100000000000000^3391 ≤ 42744116173559^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301456417 2500000000 42744116173559 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-388821883/2000000000 : ℝ), (272626223/500000000 : ℝ), (1301456417/2500000000 : ℝ)] ![(11855818875507/100000000000000 : ℝ), (11350016233137/25000000000000 : ℝ), (42744116173559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-388821883/2000000000 : ℝ)|^4415 ≤ (11855818875507/100000000000000 : ℝ)^3391
        have hw : |(-388821883/2000000000 : ℝ)|=(388821883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272626223/500000000 : ℝ)|^4415 ≤ (11350016233137/25000000000000 : ℝ)^3391
        have hw : |(272626223/500000000 : ℝ)|=(272626223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301456417/2500000000 : ℝ)|^4415 ≤ (42744116173559/100000000000000 : ℝ)^3391
        have hw : |(1301456417/2500000000 : ℝ)|=(1301456417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s2_1 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358520247/10000000000 : ℝ)*x 0 + (-2070893841/10000000000 : ℝ)*x 1 + (260291283/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358520247/10000000000 : ℝ)^4415 ≤ (44383646532303/100000000000000 : ℝ)^3391 := by
    have hnat : (5358520247 : ℕ)^4415*100000000000000^3391 ≤ 44383646532303^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358520247 10000000000 44383646532303 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070893841/10000000000 : ℝ)^4415 ≤ (1287223736359/10000000000000 : ℝ)^3391 := by
    have hnat : (2070893841 : ℕ)^4415*10000000000000^3391 ≤ 1287223736359^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070893841 10000000000 1287223736359 10000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260291283/500000000 : ℝ)^4415 ≤ (42744116088037/100000000000000 : ℝ)^3391 := by
    have hnat : (260291283 : ℕ)^4415*100000000000000^3391 ≤ 42744116088037^3391*500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260291283 500000000 42744116088037 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358520247/10000000000 : ℝ), (-2070893841/10000000000 : ℝ), (260291283/500000000 : ℝ)] ![(44383646532303/100000000000000 : ℝ), (1287223736359/10000000000000 : ℝ), (42744116088037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358520247/10000000000 : ℝ)|^4415 ≤ (44383646532303/100000000000000 : ℝ)^3391
        have hw : |(5358520247/10000000000 : ℝ)|=(5358520247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2070893841/10000000000 : ℝ)|^4415 ≤ (1287223736359/10000000000000 : ℝ)^3391
        have hw : |(-2070893841/10000000000 : ℝ)|=(2070893841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260291283/500000000 : ℝ)|^4415 ≤ (42744116088037/100000000000000 : ℝ)^3391
        have hw : |(260291283/500000000 : ℝ)|=(260291283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s2_2 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339630093/2500000000 : ℝ)*x 0 + (5205825513/10000000000 : ℝ)*x 1 + (-207089387/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339630093/2500000000 : ℝ)^4415 ≤ (44383647880307/100000000000000 : ℝ)^3391 := by
    have hnat : (1339630093 : ℕ)^4415*100000000000000^3391 ≤ 44383647880307^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339630093 2500000000 44383647880307 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5205825513/10000000000 : ℝ)^4415 ≤ (10686028629141/25000000000000 : ℝ)^3391 := by
    have hnat : (5205825513 : ℕ)^4415*25000000000000^3391 ≤ 10686028629141^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205825513 10000000000 10686028629141 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207089387/1000000000 : ℝ)^4415 ≤ (12872237598281/100000000000000 : ℝ)^3391 := by
    have hnat : (207089387 : ℕ)^4415*100000000000000^3391 ≤ 12872237598281^3391*1000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207089387 1000000000 12872237598281 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339630093/2500000000 : ℝ), (5205825513/10000000000 : ℝ), (-207089387/1000000000 : ℝ)] ![(44383647880307/100000000000000 : ℝ), (10686028629141/25000000000000 : ℝ), (12872237598281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339630093/2500000000 : ℝ)|^4415 ≤ (44383647880307/100000000000000 : ℝ)^3391
        have hw : |(1339630093/2500000000 : ℝ)|=(1339630093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5205825513/10000000000 : ℝ)|^4415 ≤ (10686028629141/25000000000000 : ℝ)^3391
        have hw : |(5205825513/10000000000 : ℝ)|=(5205825513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-207089387/1000000000 : ℝ)|^4415 ≤ (12872237598281/100000000000000 : ℝ)^3391
        have hw : |(-207089387/1000000000 : ℝ)|=(207089387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s2_3 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4294013711/10000000000 : ℝ)*x 0 + (2016062759/5000000000 : ℝ)*x 1 + (2285452929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4294013711/10000000000 : ℝ)^4415 ≤ (33265730109873/100000000000000 : ℝ)^3391 := by
    have hnat : (4294013711 : ℕ)^4415*100000000000000^3391 ≤ 33265730109873^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4294013711 10000000000 33265730109873 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016062759/5000000000 : ℝ)^4415 ≤ (30648897931769/100000000000000 : ℝ)^3391 := by
    have hnat : (2016062759 : ℕ)^4415*100000000000000^3391 ≤ 30648897931769^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016062759 5000000000 30648897931769 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285452929/5000000000 : ℝ)^4415 ≤ (36085371934113/100000000000000 : ℝ)^3391 := by
    have hnat : (2285452929 : ℕ)^4415*100000000000000^3391 ≤ 36085371934113^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285452929 5000000000 36085371934113 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4294013711/10000000000 : ℝ), (2016062759/5000000000 : ℝ), (2285452929/5000000000 : ℝ)] ![(33265730109873/100000000000000 : ℝ), (30648897931769/100000000000000 : ℝ), (36085371934113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4294013711/10000000000 : ℝ)|^4415 ≤ (33265730109873/100000000000000 : ℝ)^3391
        have hw : |(4294013711/10000000000 : ℝ)|=(4294013711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2016062759/5000000000 : ℝ)|^4415 ≤ (30648897931769/100000000000000 : ℝ)^3391
        have hw : |(2016062759/5000000000 : ℝ)|=(2016062759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2285452929/5000000000 : ℝ)|^4415 ≤ (36085371934113/100000000000000 : ℝ)^3391
        have hw : |(2285452929/5000000000 : ℝ)|=(2285452929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s2_4 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1944149727/10000000000 : ℝ)*x 0 + (5207202541/10000000000 : ℝ)*x 1 + (340696067/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1944149727/10000000000 : ℝ)^4415 ≤ (2964034737207/25000000000000 : ℝ)^3391 := by
    have hnat : (1944149727 : ℕ)^4415*25000000000000^3391 ≤ 2964034737207^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944149727 10000000000 2964034737207 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5207202541/10000000000 : ℝ)^4415 ≤ (42758835938159/100000000000000 : ℝ)^3391 := by
    have hnat : (5207202541 : ℕ)^4415*100000000000000^3391 ≤ 42758835938159^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207202541 10000000000 42758835938159 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340696067/625000000 : ℝ)^4415 ≤ (22692512549719/50000000000000 : ℝ)^3391 := by
    have hnat : (340696067 : ℕ)^4415*50000000000000^3391 ≤ 22692512549719^3391*625000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340696067 625000000 22692512549719 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1944149727/10000000000 : ℝ), (5207202541/10000000000 : ℝ), (340696067/625000000 : ℝ)] ![(2964034737207/25000000000000 : ℝ), (42758835938159/100000000000000 : ℝ), (22692512549719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1944149727/10000000000 : ℝ)|^4415 ≤ (2964034737207/25000000000000 : ℝ)^3391
        have hw : |(-1944149727/10000000000 : ℝ)|=(1944149727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5207202541/10000000000 : ℝ)|^4415 ≤ (42758835938159/100000000000000 : ℝ)^3391
        have hw : |(5207202541/10000000000 : ℝ)|=(5207202541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340696067/625000000 : ℝ)|^4415 ≤ (22692512549719/50000000000000 : ℝ)^3391
        have hw : |(340696067/625000000 : ℝ)|=(340696067/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s2_5 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529421673/1000000000 : ℝ)*x 0 + (-456395159/2500000000 : ℝ)*x 1 + (1090227689/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529421673/1000000000 : ℝ)^4415 ≤ (43691455562501/100000000000000 : ℝ)^3391 := by
    have hnat : (529421673 : ℕ)^4415*100000000000000^3391 ≤ 43691455562501^3391*1000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529421673 1000000000 43691455562501 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456395159/2500000000 : ℝ)^4415 ≤ (682719027069/6250000000000 : ℝ)^3391 := by
    have hnat : (456395159 : ℕ)^4415*6250000000000^3391 ≤ 682719027069^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456395159 2500000000 682719027069 6250000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090227689/2000000000 : ℝ)^4415 ≤ (5673129997841/12500000000000 : ℝ)^3391 := by
    have hnat : (1090227689 : ℕ)^4415*12500000000000^3391 ≤ 5673129997841^3391*2000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090227689 2000000000 5673129997841 12500000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529421673/1000000000 : ℝ), (-456395159/2500000000 : ℝ), (1090227689/2000000000 : ℝ)] ![(43691455562501/100000000000000 : ℝ), (682719027069/6250000000000 : ℝ), (5673129997841/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529421673/1000000000 : ℝ)|^4415 ≤ (43691455562501/100000000000000 : ℝ)^3391
        have hw : |(529421673/1000000000 : ℝ)|=(529421673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-456395159/2500000000 : ℝ)|^4415 ≤ (682719027069/6250000000000 : ℝ)^3391
        have hw : |(-456395159/2500000000 : ℝ)|=(456395159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090227689/2000000000 : ℝ)|^4415 ≤ (5673129997841/12500000000000 : ℝ)^3391
        have hw : |(1090227689/2000000000 : ℝ)|=(1090227689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s2_6 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323553919/2500000000 : ℝ)*x 0 + (2725568821/5000000000 : ℝ)*x 1 + (-228197901/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323553919/2500000000 : ℝ)^4415 ≤ (21845722118749/50000000000000 : ℝ)^3391 := by
    have hnat : (1323553919 : ℕ)^4415*50000000000000^3391 ≤ 21845722118749^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323553919 2500000000 21845722118749 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725568821/5000000000 : ℝ)^4415 ≤ (22692515639113/50000000000000 : ℝ)^3391 := by
    have hnat : (2725568821 : ℕ)^4415*50000000000000^3391 ≤ 22692515639113^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725568821 5000000000 22692515639113 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228197901/1250000000 : ℝ)^4415 ≤ (170680069847/1562500000000 : ℝ)^3391 := by
    have hnat : (228197901 : ℕ)^4415*1562500000000^3391 ≤ 170680069847^3391*1250000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228197901 1250000000 170680069847 1562500000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323553919/2500000000 : ℝ), (2725568821/5000000000 : ℝ), (-228197901/1250000000 : ℝ)] ![(21845722118749/50000000000000 : ℝ), (22692515639113/50000000000000 : ℝ), (170680069847/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323553919/2500000000 : ℝ)|^4415 ≤ (21845722118749/50000000000000 : ℝ)^3391
        have hw : |(1323553919/2500000000 : ℝ)|=(1323553919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725568821/5000000000 : ℝ)|^4415 ≤ (22692515639113/50000000000000 : ℝ)^3391
        have hw : |(2725568821/5000000000 : ℝ)|=(2725568821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-228197901/1250000000 : ℝ)|^4415 ≤ (170680069847/1562500000000 : ℝ)^3391
        have hw : |(-228197901/1250000000 : ℝ)|=(228197901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s2_7 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2147051639/5000000000 : ℝ)*x 0 + (2283951219/5000000000 : ℝ)*x 1 + (4035152931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147051639/5000000000 : ℝ)^4415 ≤ (33266633522063/100000000000000 : ℝ)^3391 := by
    have hnat : (2147051639 : ℕ)^4415*100000000000000^3391 ≤ 33266633522063^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147051639 5000000000 33266633522063 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2283951219/5000000000 : ℝ)^4415 ≤ (9013626049111/25000000000000 : ℝ)^3391 := by
    have hnat : (2283951219 : ℕ)^4415*25000000000000^3391 ≤ 9013626049111^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283951219 5000000000 9013626049111 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035152931/10000000000 : ℝ)^4415 ≤ (30678862265951/100000000000000 : ℝ)^3391 := by
    have hnat : (4035152931 : ℕ)^4415*100000000000000^3391 ≤ 30678862265951^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035152931 10000000000 30678862265951 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2147051639/5000000000 : ℝ), (2283951219/5000000000 : ℝ), (4035152931/10000000000 : ℝ)] ![(33266633522063/100000000000000 : ℝ), (9013626049111/25000000000000 : ℝ), (30678862265951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2147051639/5000000000 : ℝ)|^4415 ≤ (33266633522063/100000000000000 : ℝ)^3391
        have hw : |(2147051639/5000000000 : ℝ)|=(2147051639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2283951219/5000000000 : ℝ)|^4415 ≤ (9013626049111/25000000000000 : ℝ)^3391
        have hw : |(2283951219/5000000000 : ℝ)|=(2283951219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035152931/10000000000 : ℝ)|^4415 ≤ (30678862265951/100000000000000 : ℝ)^3391
        have hw : |(4035152931/10000000000 : ℝ)|=(4035152931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1455_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3931/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5251/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15723/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3931/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3931/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3931/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3931/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3931/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3931/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3931/50000 : ℝ) ^ (2207/512 : ℝ) ≤ (867188278750891/50000000000000000000 : ℝ) := by
    have hpowers : (3931/50000 : ℝ)^2207 ≤ (867188278750891/50000000000000000000 : ℝ)^512 := by
      have hnat : (3931 : ℕ)^2207*50000000000000000000^512 ≤ 867188278750891^512*50000^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3931 50000 867188278750891 50000000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3931/50000 : ℝ)) (X := (867188278750891/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hpowhi : (18677/100000 : ℝ) ^ (2207/512 : ℝ) ≤ (14453238648533829/20000000000000000000 : ℝ) := by
    have hpowers : (18677/100000 : ℝ)^2207 ≤ (14453238648533829/20000000000000000000 : ℝ)^512 := by
      have hnat : (18677 : ℕ)^2207*20000000000000000000^512 ≤ 14453238648533829^512*100000^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18677 100000 14453238648533829 20000000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18677/100000 : ℝ)) (X := (14453238648533829/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000867188278750891/25000000000000000000 : ℝ) ≤ (625005029389269/625000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (25000867188278750891/25000000000000000000 : ℝ)^512 ≤ (625005029389269/625000000000000 : ℝ)^2207 := by
      have hnat : (25000867188278750891 : ℕ)^512*625000000000000^2207 ≤ 625005029389269^2207*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000867188278750891 25000000000000000000 625005029389269 625000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625005029389269/625000000000000 : ℝ)) (X := (25000867188278750891/25000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100074000569800170927/100000000000000000000 : ℝ) ≤ (10001716245122719/10000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (100074000569800170927/100000000000000000000 : ℝ)^512 ≤ (10001716245122719/10000000000000000 : ℝ)^2207 := by
      have hnat : (100074000569800170927 : ℕ)^512*10000000000000000^2207 ≤ 10001716245122719^2207*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100074000569800170927 100000000000000000000 10001716245122719 10000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001716245122719/10000000000000000 : ℝ)) (X := (100074000569800170927/100000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10014453238648533829/10000000000000000000 : ℝ) ≤ (5001676010008567/5000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (10014453238648533829/10000000000000000000 : ℝ)^512 ≤ (5001676010008567/5000000000000000 : ℝ)^2207 := by
      have hnat : (10014453238648533829 : ℕ)^512*5000000000000000^2207 ≤ 5001676010008567^2207*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10014453238648533829 10000000000000000000 5001676010008567 5000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001676010008567/5000000000000000 : ℝ)) (X := (10014453238648533829/10000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(867188278750891/50000000000000000000 : ℝ) ≤ ((1081251493610793263/1081500000000000000 : ℝ)+2*(327154978883/216300000000000 : ℝ)*(3931/50000 : ℝ))^(2207/512 : ℝ) := by
    rw [show (1081251493610793263/1081500000000000000 : ℝ)+2*(327154978883/216300000000000 : ℝ)*(3931/50000 : ℝ)=(625005029389269/625000000000000 : ℝ) by norm_num, show 1+2*(867188278750891/50000000000000000000 : ℝ)=(25000867188278750891/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14453238648533829/20000000000000000000 : ℝ)+(867188278750891/50000000000000000000 : ℝ) ≤ ((1081251493610793263/1081500000000000000 : ℝ)+(327154978883/216300000000000 : ℝ)*((18677/100000 : ℝ)+(3931/50000 : ℝ)))^(2207/512 : ℝ) := by
    rw [show (1081251493610793263/1081500000000000000 : ℝ)+(327154978883/216300000000000 : ℝ)*((18677/100000 : ℝ)+(3931/50000 : ℝ))=(10001716245122719/10000000000000000 : ℝ) by norm_num, show 1+(14453238648533829/20000000000000000000 : ℝ)+(867188278750891/50000000000000000000 : ℝ)=(100074000569800170927/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14453238648533829/20000000000000000000 : ℝ) ≤ ((1081251493610793263/1081500000000000000 : ℝ)+2*(327154978883/216300000000000 : ℝ)*(18677/100000 : ℝ))^(2207/512 : ℝ) := by
    rw [show (1081251493610793263/1081500000000000000 : ℝ)+2*(327154978883/216300000000000 : ℝ)*(18677/100000 : ℝ)=(5001676010008567/5000000000000000 : ℝ) by norm_num, show 1+2*(14453238648533829/20000000000000000000 : ℝ)=(10014453238648533829/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1081251493610793263/1081500000000000000 : ℝ)*(X 1 0+X 2 0)+(327154978883/216300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (3931/50000 : ℝ)) (hi := (18677/100000 : ℝ)) (c := (1081251493610793263/1081500000000000000 : ℝ)) (alpha := (327154978883/216300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1081251493610793263/1081500000000000000 : ℝ)*(X 0 1+X 2 1)+(327154978883/216300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (3931/50000 : ℝ)) (hi := (18677/100000 : ℝ)) (c := (1081251493610793263/1081500000000000000 : ℝ)) (alpha := (327154978883/216300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1081251493610793263/1081500000000000000 : ℝ)*(X 0 2+X 1 2)+(327154978883/216300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (3931/50000 : ℝ)) (hi := (18677/100000 : ℝ)) (c := (1081251493610793263/1081500000000000000 : ℝ)) (alpha := (327154978883/216300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-388821883/2000000000 : ℝ)*X 0 0+(272626223/500000000 : ℝ)*X 0 1+(1301456417/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358520247/10000000000 : ℝ)*X 1 0+(-2070893841/10000000000 : ℝ)*X 1 1+(260291283/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1339630093/2500000000 : ℝ)*X 2 0+(5205825513/10000000000 : ℝ)*X 2 1+(-207089387/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4294013711/10000000000 : ℝ)*X 0 0+(2016062759/5000000000 : ℝ)*X 0 1+(2285452929/5000000000 : ℝ)*X 0 2+(4294013711/10000000000 : ℝ)*X 1 0+(2016062759/5000000000 : ℝ)*X 1 1+(2285452929/5000000000 : ℝ)*X 1 2+(4294013711/10000000000 : ℝ)*X 2 0+(2016062759/5000000000 : ℝ)*X 2 1+(2285452929/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1944149727/10000000000 : ℝ)*X 0 0+(5207202541/10000000000 : ℝ)*X 0 1+(340696067/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529421673/1000000000 : ℝ)*X 1 0+(-456395159/2500000000 : ℝ)*X 1 1+(1090227689/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323553919/2500000000 : ℝ)*X 2 0+(2725568821/5000000000 : ℝ)*X 2 1+(-228197901/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2147051639/5000000000 : ℝ)*X 0 0+(2283951219/5000000000 : ℝ)*X 0 1+(4035152931/10000000000 : ℝ)*X 0 2+(2147051639/5000000000 : ℝ)*X 1 0+(2283951219/5000000000 : ℝ)*X 1 1+(4035152931/10000000000 : ℝ)*X 1 2+(2147051639/5000000000 : ℝ)*X 2 0+(2283951219/5000000000 : ℝ)*X 2 1+(4035152931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4559849538577509738873/721000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3363063/250000000000 : ℝ)*(base19) + (1364973441/100000000000000 : ℝ)*(base23) + (10021849/25000000000000 : ℝ)*(lower2) + (183455267/100000000000000 : ℝ)*(upper3) + (23254823/20000000000000 : ℝ)*(upper5) + (295481309632671/10000000000000 : ℝ)*(major0) + (295481309632671/10000000000000 : ℝ)*(major1) + (295481309632671/10000000000000 : ℝ)*(major2) + (405354529323419/10000000000000 : ℝ)*(sp0) + (405356262738091/10000000000000 : ℝ)*(sp1) + (405356260763267/10000000000000 : ℝ)*(sp2) + (928026191148721/50000000000000 : ℝ)*(sp3) + (233492149/1250000000000 : ℝ)*(sp4) + (9626938511/100000000000000 : ℝ)*(sp7) + (1856062009235953/100000000000000 : ℝ)*(f.failure) + (405356397260611/10000000000000 : ℝ)*(f.sum) + (18377301837/11265625000000000000000000 : ℝ)*base66 + (2622074678216509/3605000000000000000000000000000 : ℝ)*base68 + (14623534260768491/3605000000000000000000000000000 : ℝ)*base69 + (36109684115203491/3605000000000000000000000000000 : ℝ)*base71 + (2141085247941/360500000000000000000000000 : ℝ)*base74 + (7243582159568491/3605000000000000000000000000000 : ℝ)*base75 + (43457959719146509/3605000000000000000000000000000 : ℝ)*base78 + (11371314470166509/3605000000000000000000000000000 : ℝ)*base80 + (139617506829/144200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3676731/10000000000000000000000 : ℝ)*base90 + (3676731/10000000000000000000000 : ℝ)*base92 + (3676731/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5488277704713663465204321/643750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (644882423/100000000000000 : ℝ)*(base19) + (56852381/100000000000000 : ℝ)*(base23) + (12971587/10000000000000 : ℝ)*(upper3) + (34091739/10000000000000 : ℝ)*(lower4) + (1494132382112769/50000000000000 : ℝ)*(major0) + (1494132382112769/50000000000000 : ℝ)*(major1) + (1494132382112769/50000000000000 : ℝ)*(major2) + (924295579/20000000000000 : ℝ)*(sp0) + (427952347/1250000000000 : ℝ)*(sp1) + (291774543/2500000000000 : ℝ)*(sp3) + (4099449991805391/100000000000000 : ℝ)*(sp4) + (2049709866106551/50000000000000 : ℝ)*(sp5) + (819890911286181/20000000000000 : ℝ)*(sp6) + (1877062960003399/100000000000000 : ℝ)*(sp7) + (938537315492559/50000000000000 : ℝ)*(f.failure) + (2049727306641643/50000000000000 : ℝ)*(f.sum) + (166299652587/257500000000000000000000000 : ℝ)*base65 + (18627612155326893/2575000000000000000000000000000 : ℝ)*base68 + (13638457696926893/2575000000000000000000000000000 : ℝ)*base70 + (4804501416998107/2575000000000000000000000000000 : ℝ)*base71 + (289949482847/64375000000000000000000000 : ℝ)*base74 + (23566792440276893/2575000000000000000000000000000 : ℝ)*base76 + (13927834603001893/2575000000000000000000000000000 : ℝ)*base78 + (29927010286251893/2575000000000000000000000000000 : ℝ)*base80 + (224583293239/515000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10617093/5000000000000000000000 : ℝ)*base90 + (10617093/5000000000000000000000 : ℝ)*base92 + (10617093/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1455_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3931/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5251/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15723/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1455_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1455_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5251/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15723/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1455_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1455_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1455_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5251/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15723/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1455_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
