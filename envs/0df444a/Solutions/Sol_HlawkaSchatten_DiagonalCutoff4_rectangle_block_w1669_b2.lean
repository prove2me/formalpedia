-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1669_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:25:18.066588+00:00
-- url     : https://prove2.me/submissions/bb227445-66b0-4c22-919f-b0427b0f66c4

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
theorem support_rectangle_w1669_box_0 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1284152/9765625 : ℝ)*x 0 + (108068633/200000000 : ℝ)*x 1 + (2701715739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1284152/9765625 : ℝ)^4995 ≤ (3896563476611/50000000000000 : ℝ)^3971 := by
    have hnat : (1284152 : ℕ)^4995*50000000000000^3971 ≤ 3896563476611^3971*9765625^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284152 9765625 3896563476611 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108068633/200000000 : ℝ)^4995 ≤ (23051718718407/50000000000000 : ℝ)^3971 := by
    have hnat : (108068633 : ℕ)^4995*50000000000000^3971 ≤ 23051718718407^3971*200000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108068633 200000000 23051718718407 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701715739/5000000000 : ℝ)^4995 ≤ (46103435590831/100000000000000 : ℝ)^3971 := by
    have hnat : (2701715739 : ℕ)^4995*100000000000000^3971 ≤ 46103435590831^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701715739 5000000000 46103435590831 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1284152/9765625 : ℝ), (108068633/200000000 : ℝ), (2701715739/5000000000 : ℝ)] ![(3896563476611/50000000000000 : ℝ), (23051718718407/50000000000000 : ℝ), (46103435590831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1284152/9765625 : ℝ)|^4995 ≤ (3896563476611/50000000000000 : ℝ)^3971
        have hw : |(-1284152/9765625 : ℝ)|=(1284152/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108068633/200000000 : ℝ)|^4995 ≤ (23051718718407/50000000000000 : ℝ)^3971
        have hw : |(108068633/200000000 : ℝ)|=(108068633/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701715739/5000000000 : ℝ)|^4995 ≤ (46103435590831/100000000000000 : ℝ)^3971
        have hw : |(2701715739/5000000000 : ℝ)|=(2701715739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_1 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250713099/10000000000 : ℝ)*x 0 + (-305936367/2000000000 : ℝ)*x 1 + (5403431737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250713099/10000000000 : ℝ)^4995 ≤ (8894081391601/20000000000000 : ℝ)^3971 := by
    have hnat : (5250713099 : ℕ)^4995*20000000000000^3971 ≤ 8894081391601^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250713099 10000000000 8894081391601 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (305936367/2000000000 : ℝ)^4995 ≤ (2356538664041/25000000000000 : ℝ)^3971 := by
    have hnat : (305936367 : ℕ)^4995*25000000000000^3971 ≤ 2356538664041^3971*2000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305936367 2000000000 2356538664041 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403431737/10000000000 : ℝ)^4995 ≤ (23051719185269/50000000000000 : ℝ)^3971 := by
    have hnat : (5403431737 : ℕ)^4995*50000000000000^3971 ≤ 23051719185269^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403431737 10000000000 23051719185269 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250713099/10000000000 : ℝ), (-305936367/2000000000 : ℝ), (5403431737/10000000000 : ℝ)] ![(8894081391601/20000000000000 : ℝ), (2356538664041/25000000000000 : ℝ), (23051719185269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250713099/10000000000 : ℝ)|^4995 ≤ (8894081391601/20000000000000 : ℝ)^3971
        have hw : |(5250713099/10000000000 : ℝ)|=(5250713099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-305936367/2000000000 : ℝ)|^4995 ≤ (2356538664041/25000000000000 : ℝ)^3971
        have hw : |(-305936367/2000000000 : ℝ)|=(305936367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403431737/10000000000 : ℝ)|^4995 ≤ (23051719185269/50000000000000 : ℝ)^3971
        have hw : |(5403431737/10000000000 : ℝ)|=(5403431737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_2 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050142613/2000000000 : ℝ)*x 0 + (5403431733/10000000000 : ℝ)*x 1 + (-1529681887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050142613/2000000000 : ℝ)^4995 ≤ (44470406595789/100000000000000 : ℝ)^3971 := by
    have hnat : (1050142613 : ℕ)^4995*100000000000000^3971 ≤ 44470406595789^3971*2000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050142613 2000000000 44470406595789 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403431733/10000000000 : ℝ)^4995 ≤ (5762929790951/12500000000000 : ℝ)^3971 := by
    have hnat : (5403431733 : ℕ)^4995*12500000000000^3971 ≤ 5762929790951^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403431733 10000000000 5762929790951 12500000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1529681887/10000000000 : ℝ)^4995 ≤ (9426155059227/100000000000000 : ℝ)^3971 := by
    have hnat : (1529681887 : ℕ)^4995*100000000000000^3971 ≤ 9426155059227^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529681887 10000000000 9426155059227 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050142613/2000000000 : ℝ), (5403431733/10000000000 : ℝ), (-1529681887/10000000000 : ℝ)] ![(44470406595789/100000000000000 : ℝ), (5762929790951/12500000000000 : ℝ), (9426155059227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050142613/2000000000 : ℝ)|^4995 ≤ (44470406595789/100000000000000 : ℝ)^3971
        have hw : |(1050142613/2000000000 : ℝ)|=(1050142613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403431733/10000000000 : ℝ)|^4995 ≤ (5762929790951/12500000000000 : ℝ)^3971
        have hw : |(5403431733/10000000000 : ℝ)|=(5403431733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1529681887/10000000000 : ℝ)|^4995 ≤ (9426155059227/100000000000000 : ℝ)^3971
        have hw : |(-1529681887/10000000000 : ℝ)|=(1529681887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_3 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4442032193/10000000000 : ℝ)*x 0 + (404033253/1000000000 : ℝ)*x 1 + (2020166601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4442032193/10000000000 : ℝ)^4995 ≤ (18016638165827/50000000000000 : ℝ)^3971 := by
    have hnat : (4442032193 : ℕ)^4995*50000000000000^3971 ≤ 18016638165827^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4442032193 10000000000 18016638165827 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404033253/1000000000 : ℝ)^4995 ≤ (15991679239157/50000000000000 : ℝ)^3971 := by
    have hnat : (404033253 : ℕ)^4995*50000000000000^3971 ≤ 15991679239157^3971*1000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404033253 1000000000 15991679239157 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2020166601/5000000000 : ℝ)^4995 ≤ (6396673033927/20000000000000 : ℝ)^3971 := by
    have hnat : (2020166601 : ℕ)^4995*20000000000000^3971 ≤ 6396673033927^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020166601 5000000000 6396673033927 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4442032193/10000000000 : ℝ), (404033253/1000000000 : ℝ), (2020166601/5000000000 : ℝ)] ![(18016638165827/50000000000000 : ℝ), (15991679239157/50000000000000 : ℝ), (6396673033927/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4442032193/10000000000 : ℝ)|^4995 ≤ (18016638165827/50000000000000 : ℝ)^3971
        have hw : |(4442032193/10000000000 : ℝ)|=(4442032193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(404033253/1000000000 : ℝ)|^4995 ≤ (15991679239157/50000000000000 : ℝ)^3971
        have hw : |(404033253/1000000000 : ℝ)|=(404033253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2020166601/5000000000 : ℝ)|^4995 ≤ (6396673033927/20000000000000 : ℝ)^3971
        have hw : |(2020166601/5000000000 : ℝ)|=(2020166601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_4 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-914108483/5000000000 : ℝ)*x 0 + (2608056121/5000000000 : ℝ)*x 1 + (5216112163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (914108483/5000000000 : ℝ)^4995 ≤ (2359158671587/20000000000000 : ℝ)^3971 := by
    have hnat : (914108483 : ℕ)^4995*20000000000000^3971 ≤ 2359158671587^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914108483 5000000000 2359158671587 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608056121/5000000000 : ℝ)^4995 ≤ (44102103735933/100000000000000 : ℝ)^3971 := by
    have hnat : (2608056121 : ℕ)^4995*100000000000000^3971 ≤ 44102103735933^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608056121 5000000000 44102103735933 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216112163/10000000000 : ℝ)^4995 ≤ (11025525723937/25000000000000 : ℝ)^3971 := by
    have hnat : (5216112163 : ℕ)^4995*25000000000000^3971 ≤ 11025525723937^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216112163 10000000000 11025525723937 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-914108483/5000000000 : ℝ), (2608056121/5000000000 : ℝ), (5216112163/10000000000 : ℝ)] ![(2359158671587/20000000000000 : ℝ), (44102103735933/100000000000000 : ℝ), (11025525723937/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-914108483/5000000000 : ℝ)|^4995 ≤ (2359158671587/20000000000000 : ℝ)^3971
        have hw : |(-914108483/5000000000 : ℝ)|=(914108483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608056121/5000000000 : ℝ)|^4995 ≤ (44102103735933/100000000000000 : ℝ)^3971
        have hw : |(2608056121/5000000000 : ℝ)|=(2608056121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216112163/10000000000 : ℝ)|^4995 ≤ (11025525723937/25000000000000 : ℝ)^3971
        have hw : |(5216112163/10000000000 : ℝ)|=(5216112163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_5 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378961399/10000000000 : ℝ)*x 0 + (-1610515823/10000000000 : ℝ)*x 1 + (652014049/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378961399/10000000000 : ℝ)^4995 ≤ (22920482491651/50000000000000 : ℝ)^3971 := by
    have hnat : (5378961399 : ℕ)^4995*50000000000000^3971 ≤ 22920482491651^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378961399 10000000000 22920482491651 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1610515823/10000000000 : ℝ)^4995 ≤ (5028464835073/50000000000000 : ℝ)^3971 := by
    have hnat : (1610515823 : ℕ)^4995*50000000000000^3971 ≤ 5028464835073^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1610515823 10000000000 5028464835073 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652014049/1250000000 : ℝ)^4995 ≤ (22051052665611/50000000000000 : ℝ)^3971 := by
    have hnat : (652014049 : ℕ)^4995*50000000000000^3971 ≤ 22051052665611^3971*1250000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652014049 1250000000 22051052665611 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378961399/10000000000 : ℝ), (-1610515823/10000000000 : ℝ), (652014049/1250000000 : ℝ)] ![(22920482491651/50000000000000 : ℝ), (5028464835073/50000000000000 : ℝ), (22051052665611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378961399/10000000000 : ℝ)|^4995 ≤ (22920482491651/50000000000000 : ℝ)^3971
        have hw : |(5378961399/10000000000 : ℝ)|=(5378961399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1610515823/10000000000 : ℝ)|^4995 ≤ (5028464835073/50000000000000 : ℝ)^3971
        have hw : |(-1610515823/10000000000 : ℝ)|=(1610515823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652014049/1250000000 : ℝ)|^4995 ≤ (22051052665611/50000000000000 : ℝ)^3971
        have hw : |(652014049/1250000000 : ℝ)|=(652014049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_6 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336185107/625000000 : ℝ)*x 0 + (1304027991/2500000000 : ℝ)*x 1 + (-64420639/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336185107/625000000 : ℝ)^4995 ≤ (45840968338633/100000000000000 : ℝ)^3971 := by
    have hnat : (336185107 : ℕ)^4995*100000000000000^3971 ≤ 45840968338633^3971*625000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336185107 625000000 45840968338633 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304027991/2500000000 : ℝ)^4995 ≤ (11025525194833/25000000000000 : ℝ)^3971 := by
    have hnat : (1304027991 : ℕ)^4995*25000000000000^3971 ≤ 11025525194833^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304027991 2500000000 11025525194833 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64420639/400000000 : ℝ)^4995 ≤ (5028465432039/50000000000000 : ℝ)^3971 := by
    have hnat : (64420639 : ℕ)^4995*50000000000000^3971 ≤ 5028465432039^3971*400000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64420639 400000000 5028465432039 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336185107/625000000 : ℝ), (1304027991/2500000000 : ℝ), (-64420639/400000000 : ℝ)] ![(45840968338633/100000000000000 : ℝ), (11025525194833/25000000000000 : ℝ), (5028465432039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336185107/625000000 : ℝ)|^4995 ≤ (45840968338633/100000000000000 : ℝ)^3971
        have hw : |(336185107/625000000 : ℝ)|=(336185107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304027991/2500000000 : ℝ)|^4995 ≤ (11025525194833/25000000000000 : ℝ)^3971
        have hw : |(1304027991/2500000000 : ℝ)|=(1304027991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64420639/400000000 : ℝ)|^4995 ≤ (5028465432039/50000000000000 : ℝ)^3971
        have hw : |(-64420639/400000000 : ℝ)|=(64420639/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_7 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (776800369/2000000000 : ℝ)*x 0 + (172761227/400000000 : ℝ)*x 1 + (4319030629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (776800369/2000000000 : ℝ)^4995 ≤ (15217282423161/50000000000000 : ℝ)^3971 := by
    have hnat : (776800369 : ℕ)^4995*50000000000000^3971 ≤ 15217282423161^3971*2000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776800369 2000000000 15217282423161 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172761227/400000000 : ℝ)^4995 ≤ (6793499571/19531250000 : ℝ)^3971 := by
    have hnat : (172761227 : ℕ)^4995*19531250000^3971 ≤ 6793499571^3971*400000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172761227 400000000 6793499571 19531250000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4319030629/10000000000 : ℝ)^4995 ≤ (34782717337537/100000000000000 : ℝ)^3971 := by
    have hnat : (4319030629 : ℕ)^4995*100000000000000^3971 ≤ 34782717337537^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319030629 10000000000 34782717337537 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(776800369/2000000000 : ℝ), (172761227/400000000 : ℝ), (4319030629/10000000000 : ℝ)] ![(15217282423161/50000000000000 : ℝ), (6793499571/19531250000 : ℝ), (34782717337537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(776800369/2000000000 : ℝ)|^4995 ≤ (15217282423161/50000000000000 : ℝ)^3971
        have hw : |(776800369/2000000000 : ℝ)|=(776800369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(172761227/400000000 : ℝ)|^4995 ≤ (6793499571/19531250000 : ℝ)^3971
        have hw : |(172761227/400000000 : ℝ)|=(172761227/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4319030629/10000000000 : ℝ)|^4995 ≤ (34782717337537/100000000000000 : ℝ)^3971
        have hw : |(4319030629/10000000000 : ℝ)|=(4319030629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_8 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-859299629/5000000000 : ℝ)*x 0 + (5080965413/10000000000 : ℝ)*x 1 + (1358162767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859299629/5000000000 : ℝ)^4995 ≤ (5456566400203/50000000000000 : ℝ)^3971 := by
    have hnat : (859299629 : ℕ)^4995*50000000000000^3971 ≤ 5456566400203^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859299629 5000000000 5456566400203 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5080965413/10000000000 : ℝ)^4995 ≤ (2133480759347/5000000000000 : ℝ)^3971 := by
    have hnat : (5080965413 : ℕ)^4995*5000000000000^3971 ≤ 2133480759347^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080965413 10000000000 2133480759347 5000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358162767/2500000000 : ℝ)^4995 ≤ (46417252006287/100000000000000 : ℝ)^3971 := by
    have hnat : (1358162767 : ℕ)^4995*100000000000000^3971 ≤ 46417252006287^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358162767 2500000000 46417252006287 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-859299629/5000000000 : ℝ), (5080965413/10000000000 : ℝ), (1358162767/2500000000 : ℝ)] ![(5456566400203/50000000000000 : ℝ), (2133480759347/5000000000000 : ℝ), (46417252006287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-859299629/5000000000 : ℝ)|^4995 ≤ (5456566400203/50000000000000 : ℝ)^3971
        have hw : |(-859299629/5000000000 : ℝ)|=(859299629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5080965413/10000000000 : ℝ)|^4995 ≤ (2133480759347/5000000000000 : ℝ)^3971
        have hw : |(5080965413/10000000000 : ℝ)|=(5080965413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358162767/2500000000 : ℝ)|^4995 ≤ (46417252006287/100000000000000 : ℝ)^3971
        have hw : |(1358162767/2500000000 : ℝ)|=(1358162767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_9 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307677831/2500000000 : ℝ)*x 0 + (-1516658651/10000000000 : ℝ)*x 1 + (2716325669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307677831/2500000000 : ℝ)^4995 ≤ (11064356178641/25000000000000 : ℝ)^3971 := by
    have hnat : (1307677831 : ℕ)^4995*25000000000000^3971 ≤ 11064356178641^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307677831 2500000000 11064356178641 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1516658651/10000000000 : ℝ)^4995 ≤ (9325320368373/100000000000000 : ℝ)^3971 := by
    have hnat : (1516658651 : ℕ)^4995*100000000000000^3971 ≤ 9325320368373^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1516658651 10000000000 9325320368373 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716325669/5000000000 : ℝ)^4995 ≤ (11604313727021/25000000000000 : ℝ)^3971 := by
    have hnat : (2716325669 : ℕ)^4995*25000000000000^3971 ≤ 11604313727021^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716325669 5000000000 11604313727021 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307677831/2500000000 : ℝ), (-1516658651/10000000000 : ℝ), (2716325669/5000000000 : ℝ)] ![(11064356178641/25000000000000 : ℝ), (9325320368373/100000000000000 : ℝ), (11604313727021/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307677831/2500000000 : ℝ)|^4995 ≤ (11064356178641/25000000000000 : ℝ)^3971
        have hw : |(1307677831/2500000000 : ℝ)|=(1307677831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1516658651/10000000000 : ℝ)|^4995 ≤ (9325320368373/100000000000000 : ℝ)^3971
        have hw : |(-1516658651/10000000000 : ℝ)|=(1516658651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716325669/5000000000 : ℝ)|^4995 ≤ (11604313727021/25000000000000 : ℝ)^3971
        have hw : |(2716325669/5000000000 : ℝ)|=(2716325669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_10 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230711309/10000000000 : ℝ)*x 0 + (5432651683/10000000000 : ℝ)*x 1 + (-94791137/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230711309/10000000000 : ℝ)^4995 ≤ (1106435613873/2500000000000 : ℝ)^3971 := by
    have hnat : (5230711309 : ℕ)^4995*2500000000000^3971 ≤ 1106435613873^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230711309 10000000000 1106435613873 2500000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432651683/10000000000 : ℝ)^4995 ≤ (9283451723187/20000000000000 : ℝ)^3971 := by
    have hnat : (5432651683 : ℕ)^4995*20000000000000^3971 ≤ 9283451723187^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432651683 10000000000 9283451723187 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94791137/625000000 : ℝ)^4995 ≤ (9325316818407/100000000000000 : ℝ)^3971 := by
    have hnat : (94791137 : ℕ)^4995*100000000000000^3971 ≤ 9325316818407^3971*625000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94791137 625000000 9325316818407 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230711309/10000000000 : ℝ), (5432651683/10000000000 : ℝ), (-94791137/625000000 : ℝ)] ![(1106435613873/2500000000000 : ℝ), (9283451723187/20000000000000 : ℝ), (9325316818407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230711309/10000000000 : ℝ)|^4995 ≤ (1106435613873/2500000000000 : ℝ)^3971
        have hw : |(5230711309/10000000000 : ℝ)|=(5230711309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432651683/10000000000 : ℝ)|^4995 ≤ (9283451723187/20000000000000 : ℝ)^3971
        have hw : |(5432651683/10000000000 : ℝ)|=(5432651683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94791137/625000000 : ℝ)|^4995 ≤ (9325316818407/100000000000000 : ℝ)^3971
        have hw : |(-94791137/625000000 : ℝ)|=(94791137/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_11 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (905341921/2000000000 : ℝ)*x 0 + (3996779607/10000000000 : ℝ)*x 1 + (499597481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (905341921/2000000000 : ℝ)^4995 ≤ (36899412899217/100000000000000 : ℝ)^3971 := by
    have hnat : (905341921 : ℕ)^4995*100000000000000^3971 ≤ 36899412899217^3971*2000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905341921 2000000000 36899412899217 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3996779607/10000000000 : ℝ)^4995 ≤ (31550292345461/100000000000000 : ℝ)^3971 := by
    have hnat : (3996779607 : ℕ)^4995*100000000000000^3971 ≤ 31550292345461^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3996779607 10000000000 31550292345461 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499597481/1250000000 : ℝ)^4995 ≤ (31550294738479/100000000000000 : ℝ)^3971 := by
    have hnat : (499597481 : ℕ)^4995*100000000000000^3971 ≤ 31550294738479^3971*1250000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499597481 1250000000 31550294738479 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(905341921/2000000000 : ℝ), (3996779607/10000000000 : ℝ), (499597481/1250000000 : ℝ)] ![(36899412899217/100000000000000 : ℝ), (31550292345461/100000000000000 : ℝ), (31550294738479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(905341921/2000000000 : ℝ)|^4995 ≤ (36899412899217/100000000000000 : ℝ)^3971
        have hw : |(905341921/2000000000 : ℝ)|=(905341921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3996779607/10000000000 : ℝ)|^4995 ≤ (31550292345461/100000000000000 : ℝ)^3971
        have hw : |(3996779607/10000000000 : ℝ)|=(3996779607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(499597481/1250000000 : ℝ)|^4995 ≤ (31550294738479/100000000000000 : ℝ)^3971
        have hw : |(499597481/1250000000 : ℝ)|=(499597481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_12 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1422605683/10000000000 : ℝ)*x 0 + (1383387647/2500000000 : ℝ)*x 1 + (1039268413/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1422605683/10000000000 : ℝ)^4995 ≤ (4301905155769/50000000000000 : ℝ)^3971 := by
    have hnat : (1422605683 : ℕ)^4995*50000000000000^3971 ≤ 4301905155769^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422605683 10000000000 4301905155769 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1383387647/2500000000 : ℝ)^4995 ≤ (296901524977/625000000000 : ℝ)^3971 := by
    have hnat : (1383387647 : ℕ)^4995*625000000000^3971 ≤ 296901524977^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383387647 2500000000 296901524977 625000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039268413/2000000000 : ℝ)^4995 ≤ (10972986418523/25000000000000 : ℝ)^3971 := by
    have hnat : (1039268413 : ℕ)^4995*25000000000000^3971 ≤ 10972986418523^3971*2000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039268413 2000000000 10972986418523 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1422605683/10000000000 : ℝ), (1383387647/2500000000 : ℝ), (1039268413/2000000000 : ℝ)] ![(4301905155769/50000000000000 : ℝ), (296901524977/625000000000 : ℝ), (10972986418523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1422605683/10000000000 : ℝ)|^4995 ≤ (4301905155769/50000000000000 : ℝ)^3971
        have hw : |(-1422605683/10000000000 : ℝ)|=(1422605683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1383387647/2500000000 : ℝ)|^4995 ≤ (296901524977/625000000000 : ℝ)^3971
        have hw : |(1383387647/2500000000 : ℝ)|=(1383387647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039268413/2000000000 : ℝ)|^4995 ≤ (10972986418523/25000000000000 : ℝ)^3971
        have hw : |(1039268413/2000000000 : ℝ)|=(1039268413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_13 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134812707/250000000 : ℝ)*x 0 + (-1618771803/10000000000 : ℝ)*x 1 + (2598170997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134812707/250000000 : ℝ)^4995 ≤ (45986233385251/100000000000000 : ℝ)^3971 := by
    have hnat : (134812707 : ℕ)^4995*100000000000000^3971 ≤ 45986233385251^3971*250000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134812707 250000000 45986233385251 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1618771803/10000000000 : ℝ)^4995 ≤ (2024364336651/20000000000000 : ℝ)^3971 := by
    have hnat : (1618771803 : ℕ)^4995*20000000000000^3971 ≤ 2024364336651^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1618771803 10000000000 2024364336651 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598170997/5000000000 : ℝ)^4995 ≤ (2743246557483/6250000000000 : ℝ)^3971 := by
    have hnat : (2598170997 : ℕ)^4995*6250000000000^3971 ≤ 2743246557483^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598170997 5000000000 2743246557483 6250000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134812707/250000000 : ℝ), (-1618771803/10000000000 : ℝ), (2598170997/5000000000 : ℝ)] ![(45986233385251/100000000000000 : ℝ), (2024364336651/20000000000000 : ℝ), (2743246557483/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134812707/250000000 : ℝ)|^4995 ≤ (45986233385251/100000000000000 : ℝ)^3971
        have hw : |(134812707/250000000 : ℝ)|=(134812707/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1618771803/10000000000 : ℝ)|^4995 ≤ (2024364336651/20000000000000 : ℝ)^3971
        have hw : |(-1618771803/10000000000 : ℝ)|=(1618771803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598170997/5000000000 : ℝ)|^4995 ≤ (2743246557483/6250000000000 : ℝ)^3971
        have hw : |(2598170997/5000000000 : ℝ)|=(2598170997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_14 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337031771/625000000 : ℝ)*x 0 + (5196342109/10000000000 : ℝ)*x 1 + (-1618771571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337031771/625000000 : ℝ)^4995 ≤ (9197246797191/20000000000000 : ℝ)^3971 := by
    have hnat : (337031771 : ℕ)^4995*20000000000000^3971 ≤ 9197246797191^3971*625000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337031771 625000000 9197246797191 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196342109/10000000000 : ℝ)^4995 ≤ (8778389228317/20000000000000 : ℝ)^3971 := by
    have hnat : (5196342109 : ℕ)^4995*20000000000000^3971 ≤ 8778389228317^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196342109 10000000000 8778389228317 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1618771571/10000000000 : ℝ)^4995 ≤ (10121819858533/100000000000000 : ℝ)^3971 := by
    have hnat : (1618771571 : ℕ)^4995*100000000000000^3971 ≤ 10121819858533^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1618771571 10000000000 10121819858533 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337031771/625000000 : ℝ), (5196342109/10000000000 : ℝ), (-1618771571/10000000000 : ℝ)] ![(9197246797191/20000000000000 : ℝ), (8778389228317/20000000000000 : ℝ), (10121819858533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337031771/625000000 : ℝ)|^4995 ≤ (9197246797191/20000000000000 : ℝ)^3971
        have hw : |(337031771/625000000 : ℝ)|=(337031771/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196342109/10000000000 : ℝ)|^4995 ≤ (8778389228317/20000000000000 : ℝ)^3971
        have hw : |(5196342109/10000000000 : ℝ)|=(5196342109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1618771571/10000000000 : ℝ)|^4995 ≤ (10121819858533/100000000000000 : ℝ)^3971
        have hw : |(-1618771571/10000000000 : ℝ)|=(1618771571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_box_15 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1911738321/5000000000 : ℝ)*x 0 + (4348391029/10000000000 : ℝ)*x 1 + (543548851/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1911738321/5000000000 : ℝ)^4995 ≤ (7459800178901/25000000000000 : ℝ)^3971 := by
    have hnat : (1911738321 : ℕ)^4995*25000000000000^3971 ≤ 7459800178901^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911738321 5000000000 7459800178901 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4348391029/10000000000 : ℝ)^4995 ≤ (35080400757439/100000000000000 : ℝ)^3971 := by
    have hnat : (4348391029 : ℕ)^4995*100000000000000^3971 ≤ 35080400757439^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348391029 10000000000 35080400757439 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543548851/1250000000 : ℝ)^4995 ≤ (35080398514777/100000000000000 : ℝ)^3971 := by
    have hnat : (543548851 : ℕ)^4995*100000000000000^3971 ≤ 35080398514777^3971*1250000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543548851 1250000000 35080398514777 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1911738321/5000000000 : ℝ), (4348391029/10000000000 : ℝ), (543548851/1250000000 : ℝ)] ![(7459800178901/25000000000000 : ℝ), (35080400757439/100000000000000 : ℝ), (35080398514777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1911738321/5000000000 : ℝ)|^4995 ≤ (7459800178901/25000000000000 : ℝ)^3971
        have hw : |(1911738321/5000000000 : ℝ)|=(1911738321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4348391029/10000000000 : ℝ)|^4995 ≤ (35080400757439/100000000000000 : ℝ)^3971
        have hw : |(4348391029/10000000000 : ℝ)|=(4348391029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543548851/1250000000 : ℝ)|^4995 ≤ (35080398514777/100000000000000 : ℝ)^3971
        have hw : |(543548851/1250000000 : ℝ)|=(543548851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1669_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16229/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2691/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1303/2000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5883/10000 : ℝ) ∧ (16307/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17681/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16229/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2691/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16229/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2691/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16229/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2691/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16229/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2691/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16229/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2691/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16229/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2691/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2691/25000 : ℝ) ^ (4991/1024 : ℝ) ≤ (1913449798539027/100000000000000000000 : ℝ) := by
    have hpowers : (2691/25000 : ℝ)^4991 ≤ (1913449798539027/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2691 : ℕ)^4991*100000000000000000000^1024 ≤ 1913449798539027^1024*25000^4991 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2691 25000 1913449798539027 100000000000000000000 4991 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2691/25000 : ℝ)) (X := (1913449798539027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16229/100000 : ℝ) ^ (4991/1024 : ℝ) ≤ (2831219405567107/20000000000000000000 : ℝ) := by
    have hpowers : (16229/100000 : ℝ)^4991 ≤ (2831219405567107/20000000000000000000 : ℝ)^1024 := by
      have hnat : (16229 : ℕ)^4991*20000000000000000000^1024 ≤ 2831219405567107^1024*100000^4991 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16229 100000 2831219405567107 20000000000000000000 4991 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16229/100000 : ℝ)) (X := (2831219405567107/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001913449798539027/50000000000000000000 : ℝ) ≤ (10000078515038867/10000000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (50001913449798539027/50000000000000000000 : ℝ)^1024 ≤ (10000078515038867/10000000000000000 : ℝ)^4991 := by
      have hnat : (50001913449798539027 : ℕ)^1024*10000000000000000^4991 ≤ 10000078515038867^4991*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001913449798539027 50000000000000000000 10000078515038867 10000000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000078515038867/10000000000000000 : ℝ)) (X := (50001913449798539027/50000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50008034773413187281/50000000000000000000 : ℝ) ≤ (5000164838360793/5000000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (50008034773413187281/50000000000000000000 : ℝ)^1024 ≤ (5000164838360793/5000000000000000 : ℝ)^4991 := by
      have hnat : (50008034773413187281 : ℕ)^1024*5000000000000000^4991 ≤ 5000164838360793^4991*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008034773413187281 50000000000000000000 5000164838360793 5000000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000164838360793/5000000000000000 : ℝ)) (X := (50008034773413187281/50000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10002831219405567107/10000000000000000000 : ℝ) ≤ (2000116167680861/2000000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (10002831219405567107/10000000000000000000 : ℝ)^1024 ≤ (2000116167680861/2000000000000000 : ℝ)^4991 := by
      have hnat : (10002831219405567107 : ℕ)^1024*2000000000000000^4991 ≤ 2000116167680861^4991*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002831219405567107 10000000000000000000 2000116167680861 2000000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000116167680861/2000000000000000 : ℝ)) (X := (10002831219405567107/10000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1913449798539027/100000000000000000000 : ℝ) ≤ ((54645022075981833523/54650000000000000000 : ℝ)+2*(251161682719/546500000000000 : ℝ)*(2691/25000 : ℝ))^(4991/1024 : ℝ) := by
    rw [show (54645022075981833523/54650000000000000000 : ℝ)+2*(251161682719/546500000000000 : ℝ)*(2691/25000 : ℝ)=(10000078515038867/10000000000000000 : ℝ) by norm_num, show 1+2*(1913449798539027/100000000000000000000 : ℝ)=(50001913449798539027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2831219405567107/20000000000000000000 : ℝ)+(1913449798539027/100000000000000000000 : ℝ) ≤ ((54645022075981833523/54650000000000000000 : ℝ)+(251161682719/546500000000000 : ℝ)*((16229/100000 : ℝ)+(2691/25000 : ℝ)))^(4991/1024 : ℝ) := by
    rw [show (54645022075981833523/54650000000000000000 : ℝ)+(251161682719/546500000000000 : ℝ)*((16229/100000 : ℝ)+(2691/25000 : ℝ))=(5000164838360793/5000000000000000 : ℝ) by norm_num, show 1+(2831219405567107/20000000000000000000 : ℝ)+(1913449798539027/100000000000000000000 : ℝ)=(50008034773413187281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2831219405567107/20000000000000000000 : ℝ) ≤ ((54645022075981833523/54650000000000000000 : ℝ)+2*(251161682719/546500000000000 : ℝ)*(16229/100000 : ℝ))^(4991/1024 : ℝ) := by
    rw [show (54645022075981833523/54650000000000000000 : ℝ)+2*(251161682719/546500000000000 : ℝ)*(16229/100000 : ℝ)=(2000116167680861/2000000000000000 : ℝ) by norm_num, show 1+2*(2831219405567107/20000000000000000000 : ℝ)=(10002831219405567107/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54645022075981833523/54650000000000000000 : ℝ)*(X 1 0+X 2 0)+(251161682719/546500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (2691/25000 : ℝ)) (hi := (16229/100000 : ℝ)) (c := (54645022075981833523/54650000000000000000 : ℝ)) (alpha := (251161682719/546500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54645022075981833523/54650000000000000000 : ℝ)*(X 0 1+X 2 1)+(251161682719/546500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (2691/25000 : ℝ)) (hi := (16229/100000 : ℝ)) (c := (54645022075981833523/54650000000000000000 : ℝ)) (alpha := (251161682719/546500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54645022075981833523/54650000000000000000 : ℝ)*(X 0 2+X 1 2)+(251161682719/546500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (2691/25000 : ℝ)) (hi := (16229/100000 : ℝ)) (c := (54645022075981833523/54650000000000000000 : ℝ)) (alpha := (251161682719/546500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1284152/9765625 : ℝ)*X 0 0+(108068633/200000000 : ℝ)*X 0 1+(2701715739/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5250713099/10000000000 : ℝ)*X 1 0+(-305936367/2000000000 : ℝ)*X 1 1+(5403431737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1050142613/2000000000 : ℝ)*X 2 0+(5403431733/10000000000 : ℝ)*X 2 1+(-1529681887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4442032193/10000000000 : ℝ)*X 0 0+(404033253/1000000000 : ℝ)*X 0 1+(2020166601/5000000000 : ℝ)*X 0 2+(4442032193/10000000000 : ℝ)*X 1 0+(404033253/1000000000 : ℝ)*X 1 1+(2020166601/5000000000 : ℝ)*X 1 2+(4442032193/10000000000 : ℝ)*X 2 0+(404033253/1000000000 : ℝ)*X 2 1+(2020166601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-914108483/5000000000 : ℝ)*X 0 0+(2608056121/5000000000 : ℝ)*X 0 1+(5216112163/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5378961399/10000000000 : ℝ)*X 1 0+(-1610515823/10000000000 : ℝ)*X 1 1+(652014049/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((336185107/625000000 : ℝ)*X 2 0+(1304027991/2500000000 : ℝ)*X 2 1+(-64420639/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((776800369/2000000000 : ℝ)*X 0 0+(172761227/400000000 : ℝ)*X 0 1+(4319030629/10000000000 : ℝ)*X 0 2+(776800369/2000000000 : ℝ)*X 1 0+(172761227/400000000 : ℝ)*X 1 1+(4319030629/10000000000 : ℝ)*X 1 2+(776800369/2000000000 : ℝ)*X 2 0+(172761227/400000000 : ℝ)*X 2 1+(4319030629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-859299629/5000000000 : ℝ)*X 0 0+(5080965413/10000000000 : ℝ)*X 0 1+(1358162767/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1307677831/2500000000 : ℝ)*X 1 0+(-1516658651/10000000000 : ℝ)*X 1 1+(2716325669/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230711309/10000000000 : ℝ)*X 2 0+(5432651683/10000000000 : ℝ)*X 2 1+(-94791137/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((905341921/2000000000 : ℝ)*X 0 0+(3996779607/10000000000 : ℝ)*X 0 1+(499597481/1250000000 : ℝ)*X 0 2+(905341921/2000000000 : ℝ)*X 1 0+(3996779607/10000000000 : ℝ)*X 1 1+(499597481/1250000000 : ℝ)*X 1 2+(905341921/2000000000 : ℝ)*X 2 0+(3996779607/10000000000 : ℝ)*X 2 1+(499597481/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1422605683/10000000000 : ℝ)*X 0 0+(1383387647/2500000000 : ℝ)*X 0 1+(1039268413/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((134812707/250000000 : ℝ)*X 1 0+(-1618771803/10000000000 : ℝ)*X 1 1+(2598170997/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((337031771/625000000 : ℝ)*X 2 0+(5196342109/10000000000 : ℝ)*X 2 1+(-1618771571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1911738321/5000000000 : ℝ)*X 0 0+(4348391029/10000000000 : ℝ)*X 0 1+(543548851/1250000000 : ℝ)*X 0 2+(1911738321/5000000000 : ℝ)*X 1 0+(4348391029/10000000000 : ℝ)*X 1 1+(543548851/1250000000 : ℝ)*X 1 2+(1911738321/5000000000 : ℝ)*X 2 0+(4348391029/10000000000 : ℝ)*X 2 1+(543548851/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1303/2000 : ℝ) ≤ (-890083835607452019998925762366429/1366250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7932767/50000000000000 : ℝ)*(upper1) + (6867427/50000000000000 : ℝ)*(upper3) + (36539759/100000000000000 : ℝ)*(upper5) + (897435703966647/50000000000000 : ℝ)*(major0) + (897435703966647/50000000000000 : ℝ)*(major1) + (897435703966647/50000000000000 : ℝ)*(major2) + (2394028277/50000000000000 : ℝ)*(sp2) + (1073619099/100000000000000 : ℝ)*(sp3) + (2627771740158631/100000000000000 : ℝ)*(sp4) + (131387891343239/5000000000000 : ℝ)*(sp5) + (2627768424729289/100000000000000 : ℝ)*(sp6) + (491842256016059/50000000000000 : ℝ)*(sp7) + (368156803/25000000000000 : ℝ)*(sp8) + (15385921063/100000000000000 : ℝ)*(sp13) + (983685585651217/100000000000000 : ℝ)*(f.failure) + (2627773212785843/100000000000000 : ℝ)*(f.sum) + (16544344090489/27325000000000000000000000000 : ℝ)*base66 + (11497178085032807381/2732500000000000000000000000000000 : ℝ)*base67 + (6730142989225307381/2732500000000000000000000000000000 : ℝ)*base69 + (5098889160515307381/2732500000000000000000000000000000 : ℝ)*base71 + (68244037472311/27325000000000000000000000000 : ℝ)*base73 + (10128875365452807381/2732500000000000000000000000000000 : ℝ)*base75 + (7623358694580307381/2732500000000000000000000000000000 : ℝ)*base77 + (4664118022382807381/2732500000000000000000000000000000 : ℝ)*base79 + (942448375087889/27325000000000000000000000000 : ℝ)*base82 + (20056461/10000000000000000000000 : ℝ)*base89 + (20056461/10000000000000000000000 : ℝ)*base91 + (20056461/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (5883/10000 : ℝ) ≤ (803802864813866482762742467482243/1366250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51508251/100000000000000 : ℝ)*(lower1) + (23523169/100000000000000 : ℝ)*(upper2) + (1608213/12500000000000 : ℝ)*(upper5) + (943983443840453/50000000000000 : ℝ)*(major0) + (943983443840453/50000000000000 : ℝ)*(major1) + (943983443840453/50000000000000 : ℝ)*(major2) + (272161561432213/10000000000000 : ℝ)*(sp0) + (680403641184001/25000000000000 : ℝ)*(sp1) + (544323135479341/20000000000000 : ℝ)*(sp2) + (1034706576632653/100000000000000 : ℝ)*(sp3) + (696561979/50000000000000 : ℝ)*(sp5) + (280463257/100000000000000 : ℝ)*(sp6) + (314005787/100000000000000 : ℝ)*(sp7) + (42942229/12500000000000 : ℝ)*(sp12) + (25867672265961/2500000000000 : ℝ)*(f.failure) + (1360807978929981/50000000000000 : ℝ)*(f.sum) + (72394532567843/13662500000000000000000000000 : ℝ)*base66 + (7215659626917894081/2732500000000000000000000000000000 : ℝ)*base68 + (8046369040647105919/2732500000000000000000000000000000 : ℝ)*base69 + (10321223019224605919/2732500000000000000000000000000000 : ℝ)*base71 + (169817070794411/27325000000000000000000000000 : ℝ)*base74 + (2177376068232894081/2732500000000000000000000000000000 : ℝ)*base76 + (6568262229467105919/2732500000000000000000000000000000 : ℝ)*base77 + (8836447700279605919/2732500000000000000000000000000000 : ℝ)*base79 + (141140534705761/27325000000000000000000000000 : ℝ)*base82 + (1084613/250000000000000000000 : ℝ)*base89 + (1084613/250000000000000000000 : ℝ)*base91 + (1084613/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (16307/20000 : ℝ) ≤ (1114008995842458307362527281514811/1366250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30911217/25000000000000 : ℝ)*(lower3) + (60139341/100000000000000 : ℝ)*(upper4) + (8954533/100000000000000 : ℝ)*(lower5) + (988549306183981/50000000000000 : ℝ)*(major0) + (988549306183981/50000000000000 : ℝ)*(major1) + (988549306183981/50000000000000 : ℝ)*(major2) + (2657847427/25000000000000 : ℝ)*(sp0) + (79221763077/100000000000000 : ℝ)*(sp1) + (27855319631/25000000000000 : ℝ)*(sp2) + (8364045241/25000000000000 : ℝ)*(sp3) + (568690302029307/20000000000000 : ℝ)*(sp8) + (1421691459886583/50000000000000 : ℝ)*(sp9) + (1421675360128859/50000000000000 : ℝ)*(sp10) + (270880597386929/25000000000000 : ℝ)*(sp11) + (27088896143217/2500000000000 : ℝ)*(f.failure) + (2843462141536243/100000000000000 : ℝ)*(f.sum) + (8287009631707/6831250000000000000000000000 : ℝ)*base65 + (15720058918957795063/2732500000000000000000000000000000 : ℝ)*base67 + (11714604539064704937/2732500000000000000000000000000000 : ℝ)*base70 + (11487074987617795063/2732500000000000000000000000000000 : ℝ)*base71 + (93741096151103/27325000000000000000000000000 : ℝ)*base73 + (8944650306387204937/2732500000000000000000000000000000 : ℝ)*base76 + (14979561072880295063/2732500000000000000000000000000000 : ℝ)*base77 + (23067234072000295063/2732500000000000000000000000000000 : ℝ)*base79 + (15911977768889/13662500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (92461/250000000000000000000 : ℝ)*base89 + (92461/250000000000000000000 : ℝ)*base91 + (92461/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-17681/20000 : ℝ) ≤ (-1932489151862669417748299210643/2186000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (823577/10000000000000 : ℝ)*(lower0) + (500279/2500000000000 : ℝ)*(lower1) + (559903/800000000000 : ℝ)*(lower2) + (1617722632951/80000000000 : ℝ)*(major0) + (1617722632951/80000000000 : ℝ)*(major1) + (1617722632951/80000000000 : ℝ)*(major2) + (2876371857/100000000000000 : ℝ)*(sp0) + (50900852027/100000000000000 : ℝ)*(sp5) + (11496480141/100000000000000 : ℝ)*(sp6) + (4786456347/100000000000000 : ℝ)*(sp7) + (2965523145281051/100000000000000 : ℝ)*(sp12) + (1482737560400441/50000000000000 : ℝ)*(sp13) + (92672328911649/3125000000000 : ℝ)*(sp14) + (1108243434406431/100000000000000 : ℝ)*(sp15) + (554124110431389/50000000000000 : ℝ)*(f.failure) + (741381505413227/25000000000000 : ℝ)*(f.sum) + (692126691057/546500000000000000000000000 : ℝ)*base66 + (13799937314347627/4372000000000000000000000000000 : ℝ)*base68 + (12950150406467627/4372000000000000000000000000000 : ℝ)*base70 + (28114389464683627/4372000000000000000000000000000 : ℝ)*base72 + (880791906451/1093000000000000000000000000 : ℝ)*base74 + (18791283757599627/4372000000000000000000000000000 : ℝ)*base76 + (22113149267687627/4372000000000000000000000000000 : ℝ)*base78 + (30184499592803627/4372000000000000000000000000000 : ℝ)*base80 + (1204072141103/546500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (63592937/5000000000000000000000 : ℝ)*base89 + (63592937/5000000000000000000000 : ℝ)*base91 + (63592937/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1669_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16229/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2691/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1303/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(5883/10000 : ℝ) else (16307/20000 : ℝ) ≤ X j i ∧ X j i ≤ (17681/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1669_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1669_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16229/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2691/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1303/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(5883/10000 : ℝ) else (16307/20000 : ℝ) ≤ X j i ∧ X j i ≤ (17681/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1669_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16229/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2691/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1303/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(5883/10000 : ℝ) else (16307/20000 : ℝ) ≤ X j i ∧ X j i ≤ (17681/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1669_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
