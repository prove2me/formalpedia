-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1080_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:49:00.72301+00:00
-- url     : https://prove2.me/submissions/0d312a28-08a2-473e-8849-851da01af24c

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
theorem support_rectangle_w1080_s3_0 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2192341977/10000000000 : ℝ)*x 0 + (1358978743/2500000000 : ℝ)*x 1 + (163308777/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2192341977/10000000000 : ℝ)^8273 ≤ (13306681955537/100000000000000 : ℝ)^6225 := by
    have hnat : (2192341977 : ℕ)^8273*100000000000000^6225 ≤ 13306681955537^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192341977 10000000000 13306681955537 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358978743/2500000000 : ℝ)^8273 ≤ (44481397322563/100000000000000 : ℝ)^6225 := by
    have hnat : (1358978743 : ℕ)^8273*100000000000000^6225 ≤ 44481397322563^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358978743 2500000000 44481397322563 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163308777/312500000 : ℝ)^8273 ≤ (42211920711711/100000000000000 : ℝ)^6225 := by
    have hnat : (163308777 : ℕ)^8273*100000000000000^6225 ≤ 42211920711711^6225*312500000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163308777 312500000 42211920711711 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2192341977/10000000000 : ℝ), (1358978743/2500000000 : ℝ), (163308777/312500000 : ℝ)] ![(13306681955537/100000000000000 : ℝ), (44481397322563/100000000000000 : ℝ), (42211920711711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2192341977/10000000000 : ℝ)|^8273 ≤ (13306681955537/100000000000000 : ℝ)^6225
        have hw : |(-2192341977/10000000000 : ℝ)|=(2192341977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358978743/2500000000 : ℝ)|^8273 ≤ (44481397322563/100000000000000 : ℝ)^6225
        have hw : |(1358978743/2500000000 : ℝ)|=(1358978743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163308777/312500000 : ℝ)|^8273 ≤ (42211920711711/100000000000000 : ℝ)^6225
        have hw : |(163308777/312500000 : ℝ)|=(163308777/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s3_1 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355331061/10000000000 : ℝ)*x 0 + (-2299858823/10000000000 : ℝ)*x 1 + (5225880873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355331061/10000000000 : ℝ)^8273 ≤ (21803595562669/50000000000000 : ℝ)^6225 := by
    have hnat : (5355331061 : ℕ)^8273*50000000000000^6225 ≤ 21803595562669^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355331061 10000000000 21803595562669 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2299858823/10000000000 : ℝ)^8273 ≤ (14180888049999/100000000000000 : ℝ)^6225 := by
    have hnat : (2299858823 : ℕ)^8273*100000000000000^6225 ≤ 14180888049999^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2299858823 10000000000 14180888049999 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5225880873/10000000000 : ℝ)^8273 ≤ (1688476832333/4000000000000 : ℝ)^6225 := by
    have hnat : (5225880873 : ℕ)^8273*4000000000000^6225 ≤ 1688476832333^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225880873 10000000000 1688476832333 4000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355331061/10000000000 : ℝ), (-2299858823/10000000000 : ℝ), (5225880873/10000000000 : ℝ)] ![(21803595562669/50000000000000 : ℝ), (14180888049999/100000000000000 : ℝ), (1688476832333/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355331061/10000000000 : ℝ)|^8273 ≤ (21803595562669/50000000000000 : ℝ)^6225
        have hw : |(5355331061/10000000000 : ℝ)|=(5355331061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2299858823/10000000000 : ℝ)|^8273 ≤ (14180888049999/100000000000000 : ℝ)^6225
        have hw : |(-2299858823/10000000000 : ℝ)|=(2299858823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5225880873/10000000000 : ℝ)|^8273 ≤ (1688476832333/4000000000000 : ℝ)^6225
        have hw : |(5225880873/10000000000 : ℝ)|=(5225880873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s3_2 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355331001/10000000000 : ℝ)*x 0 + (5225881283/10000000000 : ℝ)*x 1 + (-1149929183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355331001/10000000000 : ℝ)^8273 ≤ (10901797619009/25000000000000 : ℝ)^6225 := by
    have hnat : (5355331001 : ℕ)^8273*25000000000000^6225 ≤ 10901797619009^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355331001 10000000000 10901797619009 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225881283/10000000000 : ℝ)^8273 ≤ (42211925209647/100000000000000 : ℝ)^6225 := by
    have hnat : (5225881283 : ℕ)^8273*100000000000000^6225 ≤ 42211925209647^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225881283 10000000000 42211925209647 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1149929183/5000000000 : ℝ)^8273 ≤ (7090442152541/50000000000000 : ℝ)^6225 := by
    have hnat : (1149929183 : ℕ)^8273*50000000000000^6225 ≤ 7090442152541^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149929183 5000000000 7090442152541 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355331001/10000000000 : ℝ), (5225881283/10000000000 : ℝ), (-1149929183/5000000000 : ℝ)] ![(10901797619009/25000000000000 : ℝ), (42211925209647/100000000000000 : ℝ), (7090442152541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355331001/10000000000 : ℝ)|^8273 ≤ (10901797619009/25000000000000 : ℝ)^6225
        have hw : |(5355331001/10000000000 : ℝ)|=(5355331001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225881283/10000000000 : ℝ)|^8273 ≤ (42211925209647/100000000000000 : ℝ)^6225
        have hw : |(5225881283/10000000000 : ℝ)|=(5225881283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1149929183/5000000000 : ℝ)|^8273 ≤ (7090442152541/50000000000000 : ℝ)^6225
        have hw : |(-1149929183/5000000000 : ℝ)|=(1149929183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s3_3 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874157863/2000000000 : ℝ)*x 0 + (4169311391/10000000000 : ℝ)*x 1 + (229104609/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874157863/2000000000 : ℝ)^8273 ≤ (33289365258441/100000000000000 : ℝ)^6225 := by
    have hnat : (874157863 : ℕ)^8273*100000000000000^6225 ≤ 33289365258441^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874157863 2000000000 33289365258441 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169311391/10000000000 : ℝ)^8273 ≤ (7816404607611/25000000000000 : ℝ)^6225 := by
    have hnat : (4169311391 : ℕ)^8273*25000000000000^6225 ≤ 7816404607611^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169311391 10000000000 7816404607611 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229104609/500000000 : ℝ)^8273 ≤ (35445016300493/100000000000000 : ℝ)^6225 := by
    have hnat : (229104609 : ℕ)^8273*100000000000000^6225 ≤ 35445016300493^6225*500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229104609 500000000 35445016300493 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874157863/2000000000 : ℝ), (4169311391/10000000000 : ℝ), (229104609/500000000 : ℝ)] ![(33289365258441/100000000000000 : ℝ), (7816404607611/25000000000000 : ℝ), (35445016300493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874157863/2000000000 : ℝ)|^8273 ≤ (33289365258441/100000000000000 : ℝ)^6225
        have hw : |(874157863/2000000000 : ℝ)|=(874157863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169311391/10000000000 : ℝ)|^8273 ≤ (7816404607611/25000000000000 : ℝ)^6225
        have hw : |(4169311391/10000000000 : ℝ)|=(4169311391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(229104609/500000000 : ℝ)|^8273 ≤ (35445016300493/100000000000000 : ℝ)^6225
        have hw : |(229104609/500000000 : ℝ)|=(229104609/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s3_4 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-219236403/1000000000 : ℝ)*x 0 + (5226732771/10000000000 : ℝ)*x 1 + (2717528817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219236403/1000000000 : ℝ)^8273 ≤ (13306859846359/100000000000000 : ℝ)^6225 := by
    have hnat : (219236403 : ℕ)^8273*100000000000000^6225 ≤ 13306859846359^6225*1000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219236403 1000000000 13306859846359 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5226732771/10000000000 : ℝ)^8273 ≤ (42221066120227/100000000000000 : ℝ)^6225 := by
    have hnat : (5226732771 : ℕ)^8273*100000000000000^6225 ≤ 42221066120227^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226732771 10000000000 42221066120227 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717528817/5000000000 : ℝ)^8273 ≤ (44472074010073/100000000000000 : ℝ)^6225 := by
    have hnat : (2717528817 : ℕ)^8273*100000000000000^6225 ≤ 44472074010073^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717528817 5000000000 44472074010073 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219236403/1000000000 : ℝ), (5226732771/10000000000 : ℝ), (2717528817/5000000000 : ℝ)] ![(13306859846359/100000000000000 : ℝ), (42221066120227/100000000000000 : ℝ), (44472074010073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219236403/1000000000 : ℝ)|^8273 ≤ (13306859846359/100000000000000 : ℝ)^6225
        have hw : |(-219236403/1000000000 : ℝ)|=(219236403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5226732771/10000000000 : ℝ)|^8273 ≤ (42221066120227/100000000000000 : ℝ)^6225
        have hw : |(5226732771/10000000000 : ℝ)|=(5226732771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717528817/5000000000 : ℝ)|^8273 ≤ (44472074010073/100000000000000 : ℝ)^6225
        have hw : |(2717528817/5000000000 : ℝ)|=(2717528817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s3_5 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302366569/10000000000 : ℝ)*x 0 + (-2090682557/10000000000 : ℝ)*x 1 + (1358764377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302366569/10000000000 : ℝ)^8273 ≤ (43034959875391/100000000000000 : ℝ)^6225 := by
    have hnat : (5302366569 : ℕ)^8273*100000000000000^6225 ≤ 43034959875391^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302366569 10000000000 43034959875391 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2090682557/10000000000 : ℝ)^8273 ≤ (312324186759/2500000000000 : ℝ)^6225 := by
    have hnat : (2090682557 : ℕ)^8273*2500000000000^6225 ≤ 312324186759^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090682557 10000000000 312324186759 2500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358764377/2500000000 : ℝ)^8273 ≤ (22236036319947/50000000000000 : ℝ)^6225 := by
    have hnat : (1358764377 : ℕ)^8273*50000000000000^6225 ≤ 22236036319947^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358764377 2500000000 22236036319947 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302366569/10000000000 : ℝ), (-2090682557/10000000000 : ℝ), (1358764377/2500000000 : ℝ)] ![(43034959875391/100000000000000 : ℝ), (312324186759/2500000000000 : ℝ), (22236036319947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302366569/10000000000 : ℝ)|^8273 ≤ (43034959875391/100000000000000 : ℝ)^6225
        have hw : |(5302366569/10000000000 : ℝ)|=(5302366569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2090682557/10000000000 : ℝ)|^8273 ≤ (312324186759/2500000000000 : ℝ)^6225
        have hw : |(-2090682557/10000000000 : ℝ)|=(2090682557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358764377/2500000000 : ℝ)|^8273 ≤ (22236036319947/50000000000000 : ℝ)^6225
        have hw : |(1358764377/2500000000 : ℝ)|=(1358764377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s3_6 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530236691/1000000000 : ℝ)*x 0 + (339691127/625000000 : ℝ)*x 1 + (-2090681377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530236691/1000000000 : ℝ)^8273 ≤ (43034963553543/100000000000000 : ℝ)^6225 := by
    have hnat : (530236691 : ℕ)^8273*100000000000000^6225 ≤ 43034963553543^6225*1000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530236691 1000000000 43034963553543 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339691127/625000000 : ℝ)^8273 ≤ (44472078338101/100000000000000 : ℝ)^6225 := by
    have hnat : (339691127 : ℕ)^8273*100000000000000^6225 ≤ 44472078338101^6225*625000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339691127 625000000 44472078338101 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2090681377/10000000000 : ℝ)^8273 ≤ (624647904971/5000000000000 : ℝ)^6225 := by
    have hnat : (2090681377 : ℕ)^8273*5000000000000^6225 ≤ 624647904971^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090681377 10000000000 624647904971 5000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530236691/1000000000 : ℝ), (339691127/625000000 : ℝ), (-2090681377/10000000000 : ℝ)] ![(43034963553543/100000000000000 : ℝ), (44472078338101/100000000000000 : ℝ), (624647904971/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530236691/1000000000 : ℝ)|^8273 ≤ (43034963553543/100000000000000 : ℝ)^6225
        have hw : |(530236691/1000000000 : ℝ)|=(530236691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339691127/625000000 : ℝ)|^8273 ≤ (44472078338101/100000000000000 : ℝ)^6225
        have hw : |(339691127/625000000 : ℝ)|=(339691127/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2090681377/10000000000 : ℝ)|^8273 ≤ (624647904971/5000000000000 : ℝ)^6225
        have hw : |(-2090681377/10000000000 : ℝ)|=(2090681377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s3_7 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874166169/2000000000 : ℝ)*x 0 + (916083669/2000000000 : ℝ)*x 1 + (4170995633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874166169/2000000000 : ℝ)^8273 ≤ (208061160179/625000000000 : ℝ)^6225 := by
    have hnat : (874166169 : ℕ)^8273*625000000000^6225 ≤ 208061160179^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874166169 2000000000 208061160179 625000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (916083669/2000000000 : ℝ)^8273 ≤ (35427809442609/100000000000000 : ℝ)^6225 := by
    have hnat : (916083669 : ℕ)^8273*100000000000000^6225 ≤ 35427809442609^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916083669 2000000000 35427809442609 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170995633/10000000000 : ℝ)^8273 ≤ (7820601228299/25000000000000 : ℝ)^6225 := by
    have hnat : (4170995633 : ℕ)^8273*25000000000000^6225 ≤ 7820601228299^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170995633 10000000000 7820601228299 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874166169/2000000000 : ℝ), (916083669/2000000000 : ℝ), (4170995633/10000000000 : ℝ)] ![(208061160179/625000000000 : ℝ), (35427809442609/100000000000000 : ℝ), (7820601228299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874166169/2000000000 : ℝ)|^8273 ≤ (208061160179/625000000000 : ℝ)^6225
        have hw : |(874166169/2000000000 : ℝ)|=(874166169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(916083669/2000000000 : ℝ)|^8273 ≤ (35427809442609/100000000000000 : ℝ)^6225
        have hw : |(916083669/2000000000 : ℝ)|=(916083669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170995633/10000000000 : ℝ)|^8273 ≤ (7820601228299/25000000000000 : ℝ)^6225
        have hw : |(4170995633/10000000000 : ℝ)|=(4170995633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1080_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3339/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (439/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (5221/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7443/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3339/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (439/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3339/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (439/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3339/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (439/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3339/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (439/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3339/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (439/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3339/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (439/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (439/5000 : ℝ) ^ (517/128 : ℝ) ≤ (5403912622304027/100000000000000000000 : ℝ) := by
    have hpowers : (439/5000 : ℝ)^517 ≤ (5403912622304027/100000000000000000000 : ℝ)^128 := by
      have hnat : (439 : ℕ)^517*100000000000000000000^128 ≤ 5403912622304027^128*5000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        439 5000 5403912622304027 100000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (439/5000 : ℝ)) (X := (5403912622304027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hpowhi : (3339/20000 : ℝ) ^ (517/128 : ℝ) ≤ (18109980571366597/25000000000000000000 : ℝ) := by
    have hpowers : (3339/20000 : ℝ)^517 ≤ (18109980571366597/25000000000000000000 : ℝ)^128 := by
      have hnat : (3339 : ℕ)^517*25000000000000000000^128 ≤ 18109980571366597^128*20000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3339 20000 18109980571366597 25000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3339/20000 : ℝ)) (X := (18109980571366597/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005403912622304027/50000000000000000000 : ℝ) ≤ (2000053514328269/2000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (50005403912622304027/50000000000000000000 : ℝ)^128 ≤ (2000053514328269/2000000000000000 : ℝ)^517 := by
      have hnat : (50005403912622304027 : ℕ)^128*2000000000000000^517 ≤ 2000053514328269^517*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005403912622304027 50000000000000000000 2000053514328269 2000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000053514328269/2000000000000000 : ℝ)) (X := (50005403912622304027/50000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (20015568766981554083/20000000000000000000 : ℝ) ≤ (2500481677668261/2500000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (20015568766981554083/20000000000000000000 : ℝ)^128 ≤ (2500481677668261/2500000000000000 : ℝ)^517 := by
      have hnat : (20015568766981554083 : ℕ)^128*2500000000000000^517 ≤ 2500481677668261^517*20000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20015568766981554083 20000000000000000000 2500481677668261 2500000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500481677668261/2500000000000000 : ℝ)) (X := (20015568766981554083/20000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (12518109980571366597/12500000000000000000 : ℝ) ≤ (10003585849704743/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (12518109980571366597/12500000000000000000 : ℝ)^128 ≤ (10003585849704743/10000000000000000 : ℝ)^517 := by
      have hnat : (12518109980571366597 : ℕ)^128*10000000000000000^517 ≤ 10003585849704743^517*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12518109980571366597 12500000000000000000 10003585849704743 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003585849704743/10000000000000000 : ℝ)) (X := (12518109980571366597/12500000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5403912622304027/100000000000000000000 : ℝ) ≤ ((15824596669628922247/15830000000000000000 : ℝ)+2*(1659139031699/791500000000000 : ℝ)*(439/5000 : ℝ))^(517/128 : ℝ) := by
    rw [show (15824596669628922247/15830000000000000000 : ℝ)+2*(1659139031699/791500000000000 : ℝ)*(439/5000 : ℝ)=(2000053514328269/2000000000000000 : ℝ) by norm_num, show 1+2*(5403912622304027/100000000000000000000 : ℝ)=(50005403912622304027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18109980571366597/25000000000000000000 : ℝ)+(5403912622304027/100000000000000000000 : ℝ) ≤ ((15824596669628922247/15830000000000000000 : ℝ)+(1659139031699/791500000000000 : ℝ)*((3339/20000 : ℝ)+(439/5000 : ℝ)))^(517/128 : ℝ) := by
    rw [show (15824596669628922247/15830000000000000000 : ℝ)+(1659139031699/791500000000000 : ℝ)*((3339/20000 : ℝ)+(439/5000 : ℝ))=(2500481677668261/2500000000000000 : ℝ) by norm_num, show 1+(18109980571366597/25000000000000000000 : ℝ)+(5403912622304027/100000000000000000000 : ℝ)=(20015568766981554083/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18109980571366597/25000000000000000000 : ℝ) ≤ ((15824596669628922247/15830000000000000000 : ℝ)+2*(1659139031699/791500000000000 : ℝ)*(3339/20000 : ℝ))^(517/128 : ℝ) := by
    rw [show (15824596669628922247/15830000000000000000 : ℝ)+2*(1659139031699/791500000000000 : ℝ)*(3339/20000 : ℝ)=(10003585849704743/10000000000000000 : ℝ) by norm_num, show 1+2*(18109980571366597/25000000000000000000 : ℝ)=(12518109980571366597/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15824596669628922247/15830000000000000000 : ℝ)*(X 1 0+X 2 0)+(1659139031699/791500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (439/5000 : ℝ)) (hi := (3339/20000 : ℝ)) (c := (15824596669628922247/15830000000000000000 : ℝ)) (alpha := (1659139031699/791500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15824596669628922247/15830000000000000000 : ℝ)*(X 0 1+X 2 1)+(1659139031699/791500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (439/5000 : ℝ)) (hi := (3339/20000 : ℝ)) (c := (15824596669628922247/15830000000000000000 : ℝ)) (alpha := (1659139031699/791500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15824596669628922247/15830000000000000000 : ℝ)*(X 0 2+X 1 2)+(1659139031699/791500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (439/5000 : ℝ)) (hi := (3339/20000 : ℝ)) (c := (15824596669628922247/15830000000000000000 : ℝ)) (alpha := (1659139031699/791500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2192341977/10000000000 : ℝ)*X 0 0+(1358978743/2500000000 : ℝ)*X 0 1+(163308777/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355331061/10000000000 : ℝ)*X 1 0+(-2299858823/10000000000 : ℝ)*X 1 1+(5225880873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355331001/10000000000 : ℝ)*X 2 0+(5225881283/10000000000 : ℝ)*X 2 1+(-1149929183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874157863/2000000000 : ℝ)*X 0 0+(4169311391/10000000000 : ℝ)*X 0 1+(229104609/500000000 : ℝ)*X 0 2+(874157863/2000000000 : ℝ)*X 1 0+(4169311391/10000000000 : ℝ)*X 1 1+(229104609/500000000 : ℝ)*X 1 2+(874157863/2000000000 : ℝ)*X 2 0+(4169311391/10000000000 : ℝ)*X 2 1+(229104609/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219236403/1000000000 : ℝ)*X 0 0+(5226732771/10000000000 : ℝ)*X 0 1+(2717528817/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302366569/10000000000 : ℝ)*X 1 0+(-2090682557/10000000000 : ℝ)*X 1 1+(1358764377/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530236691/1000000000 : ℝ)*X 2 0+(339691127/625000000 : ℝ)*X 2 1+(-2090681377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((874166169/2000000000 : ℝ)*X 0 0+(916083669/2000000000 : ℝ)*X 0 1+(4170995633/10000000000 : ℝ)*X 0 2+(874166169/2000000000 : ℝ)*X 1 0+(916083669/2000000000 : ℝ)*X 1 1+(4170995633/10000000000 : ℝ)*X 1 2+(874166169/2000000000 : ℝ)*X 2 0+(916083669/2000000000 : ℝ)*X 2 1+(4170995633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1170458852029861673353985361/197875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1652298791/100000000000000 : ℝ)*(base19) + (60521943/5000000000000 : ℝ)*(base23) + (208063459/100000000000000 : ℝ)*(lower2) + (9228463/20000000000000 : ℝ)*(upper3) + (188381963/100000000000000 : ℝ)*(upper5) + (1795953536901821/50000000000000 : ℝ)*(major0) + (1795953536901821/50000000000000 : ℝ)*(major1) + (1795953536901821/50000000000000 : ℝ)*(major2) + (2380579680606777/50000000000000 : ℝ)*(sp0) + (4761193418897579/100000000000000 : ℝ)*(sp1) + (476119386075751/10000000000000 : ℝ)*(sp2) + (15141289930081/625000000000 : ℝ)*(sp3) + (7141996563/20000000000000 : ℝ)*(sp4) + (3122606631/25000000000000 : ℝ)*(sp7) + (605654719809871/25000000000000 : ℝ)*(f.failure) + (4761195071196369/100000000000000 : ℝ)*(f.sum) + (30754949290821/19787500000000000000000000000 : ℝ)*base66 + (4236448604800208213/791500000000000000000000000000000 : ℝ)*base68 + (6315514790947708213/791500000000000000000000000000000 : ℝ)*base70 + (47739982799208213/791500000000000000000000000000000 : ℝ)*base72 + (89883834007467/39575000000000000000000000000 : ℝ)*base74 + (14627464784889208213/791500000000000000000000000000000 : ℝ)*base76 + (6719453477024291787/791500000000000000000000000000000 : ℝ)*base77 + (7739172078345708213/791500000000000000000000000000000 : ℝ)*base80 + (172275928126821/19787500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (12987701/1250000000000000000000 : ℝ)*base89 + (12987701/1250000000000000000000 : ℝ)*base91 + (12987701/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (595643971182182744009725713/98937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1241899029/100000000000000 : ℝ)*(base19) + (468059823/20000000000000 : ℝ)*(base23) + (46422211/20000000000000 : ℝ)*(upper2) + (17108787/10000000000000 : ℝ)*(upper3) + (21456311/10000000000000 : ℝ)*(upper5) + (452666280888131/12500000000000 : ℝ)*(major0) + (452666280888131/12500000000000 : ℝ)*(major1) + (452666280888131/12500000000000 : ℝ)*(major2) + (16031877539/100000000000000 : ℝ)*(sp1) + (51266119051/100000000000000 : ℝ)*(sp2) + (960039297376967/20000000000000 : ℝ)*(sp4) + (4800179213108267/100000000000000 : ℝ)*(sp5) + (4800142880466669/100000000000000 : ℝ)*(sp6) + (610615951661259/25000000000000 : ℝ)*(sp7) + (610615951661259/25000000000000 : ℝ)*(f.failure) + (960039297376967/20000000000000 : ℝ)*(f.sum) + (47860134238099/19787500000000000000000000000 : ℝ)*base66 + (1631129602643844643/197875000000000000000000000000000 : ℝ)*base68 + (2309879432926219643/197875000000000000000000000000000 : ℝ)*base70 + (2082420546132719643/197875000000000000000000000000000 : ℝ)*base72 + (1253742420289/1236718750000000000000000000 : ℝ)*base74 + (1235032285716094643/197875000000000000000000000000000 : ℝ)*base76 + (2788291730599844643/197875000000000000000000000000000 : ℝ)*base78 + (1063214512474844643/197875000000000000000000000000000 : ℝ)*base80 + (3738689967877/39575000000000000000000000000 : ℝ)*base81 + (16568329/1250000000000000000000 : ℝ)*base89 + (16568329/1250000000000000000000 : ℝ)*base91 + (16568329/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1080_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3339/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (439/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5221/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7443/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1080_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1080_s4_0 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-109794221/500000000 : ℝ)*x 0 + (1081009873/2000000000 : ℝ)*x 1 + (1050886351/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109794221/500000000 : ℝ)^8273 ≤ (6667632332521/50000000000000 : ℝ)^6225 := by
    have hnat : (109794221 : ℕ)^8273*50000000000000^6225 ≤ 6667632332521^6225*500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109794221 500000000 6667632332521 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081009873/2000000000 : ℝ)^8273 ≤ (8829209527157/20000000000000 : ℝ)^6225 := by
    have hnat : (1081009873 : ℕ)^8273*20000000000000^6225 ≤ 8829209527157^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081009873 2000000000 8829209527157 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050886351/2000000000 : ℝ)^8273 ≤ (21259343841537/50000000000000 : ℝ)^6225 := by
    have hnat : (1050886351 : ℕ)^8273*50000000000000^6225 ≤ 21259343841537^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050886351 2000000000 21259343841537 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109794221/500000000 : ℝ), (1081009873/2000000000 : ℝ), (1050886351/2000000000 : ℝ)] ![(6667632332521/50000000000000 : ℝ), (8829209527157/20000000000000 : ℝ), (21259343841537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109794221/500000000 : ℝ)|^8273 ≤ (6667632332521/50000000000000 : ℝ)^6225
        have hw : |(-109794221/500000000 : ℝ)|=(109794221/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081009873/2000000000 : ℝ)|^8273 ≤ (8829209527157/20000000000000 : ℝ)^6225
        have hw : |(1081009873/2000000000 : ℝ)|=(1081009873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050886351/2000000000 : ℝ)|^8273 ≤ (21259343841537/50000000000000 : ℝ)^6225
        have hw : |(1050886351/2000000000 : ℝ)|=(1050886351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s4_1 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534767341/1000000000 : ℝ)*x 0 + (-284060019/1250000000 : ℝ)*x 1 + (5254431589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534767341/1000000000 : ℝ)^8273 ≤ (870486836561/2000000000000 : ℝ)^6225 := by
    have hnat : (534767341 : ℕ)^8273*2000000000000^6225 ≤ 870486836561^6225*1000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534767341 1000000000 870486836561 2000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284060019/1250000000 : ℝ)^8273 ≤ (6978486134123/50000000000000 : ℝ)^6225 := by
    have hnat : (284060019 : ℕ)^8273*50000000000000^6225 ≤ 6978486134123^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284060019 1250000000 6978486134123 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254431589/10000000000 : ℝ)^8273 ≤ (21259342948939/50000000000000 : ℝ)^6225 := by
    have hnat : (5254431589 : ℕ)^8273*50000000000000^6225 ≤ 21259342948939^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254431589 10000000000 21259342948939 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534767341/1000000000 : ℝ), (-284060019/1250000000 : ℝ), (5254431589/10000000000 : ℝ)] ![(870486836561/2000000000000 : ℝ), (6978486134123/50000000000000 : ℝ), (21259342948939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534767341/1000000000 : ℝ)|^8273 ≤ (870486836561/2000000000000 : ℝ)^6225
        have hw : |(534767341/1000000000 : ℝ)|=(534767341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-284060019/1250000000 : ℝ)|^8273 ≤ (6978486134123/50000000000000 : ℝ)^6225
        have hw : |(-284060019/1250000000 : ℝ)|=(284060019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254431589/10000000000 : ℝ)|^8273 ≤ (21259342948939/50000000000000 : ℝ)^6225
        have hw : |(5254431589/10000000000 : ℝ)|=(5254431589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s4_2 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347673523/10000000000 : ℝ)*x 0 + (1313607903/2500000000 : ℝ)*x 1 + (-2272479971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347673523/10000000000 : ℝ)^8273 ≤ (43524343050327/100000000000000 : ℝ)^6225 := by
    have hnat : (5347673523 : ℕ)^8273*100000000000000^6225 ≤ 43524343050327^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347673523 10000000000 43524343050327 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313607903/2500000000 : ℝ)^8273 ≤ (1700747445809/4000000000000 : ℝ)^6225 := by
    have hnat : (1313607903 : ℕ)^8273*4000000000000^6225 ≤ 1700747445809^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313607903 2500000000 1700747445809 4000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2272479971/10000000000 : ℝ)^8273 ≤ (6978485395431/50000000000000 : ℝ)^6225 := by
    have hnat : (2272479971 : ℕ)^8273*50000000000000^6225 ≤ 6978485395431^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272479971 10000000000 6978485395431 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347673523/10000000000 : ℝ), (1313607903/2500000000 : ℝ), (-2272479971/10000000000 : ℝ)] ![(43524343050327/100000000000000 : ℝ), (1700747445809/4000000000000 : ℝ), (6978485395431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347673523/10000000000 : ℝ)|^8273 ≤ (43524343050327/100000000000000 : ℝ)^6225
        have hw : |(5347673523/10000000000 : ℝ)|=(5347673523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313607903/2500000000 : ℝ)|^8273 ≤ (1700747445809/4000000000000 : ℝ)^6225
        have hw : |(1313607903/2500000000 : ℝ)|=(1313607903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2272479971/10000000000 : ℝ)|^8273 ≤ (6978485395431/50000000000000 : ℝ)^6225
        have hw : |(-2272479971/10000000000 : ℝ)|=(2272479971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s4_3 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874579597/2000000000 : ℝ)*x 0 + (1056855179/2500000000 : ℝ)*x 1 + (4523430941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874579597/2000000000 : ℝ)^8273 ≤ (33310711056217/100000000000000 : ℝ)^6225 := by
    have hnat : (874579597 : ℕ)^8273*100000000000000^6225 ≤ 33310711056217^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874579597 2000000000 33310711056217 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056855179/2500000000 : ℝ)^8273 ≤ (31846066895383/100000000000000 : ℝ)^6225 := by
    have hnat : (1056855179 : ℕ)^8273*100000000000000^6225 ≤ 31846066895383^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056855179 2500000000 31846066895383 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4523430941/10000000000 : ℝ)^8273 ≤ (17421611011729/50000000000000 : ℝ)^6225 := by
    have hnat : (4523430941 : ℕ)^8273*50000000000000^6225 ≤ 17421611011729^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523430941 10000000000 17421611011729 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874579597/2000000000 : ℝ), (1056855179/2500000000 : ℝ), (4523430941/10000000000 : ℝ)] ![(33310711056217/100000000000000 : ℝ), (31846066895383/100000000000000 : ℝ), (17421611011729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874579597/2000000000 : ℝ)|^8273 ≤ (33310711056217/100000000000000 : ℝ)^6225
        have hw : |(874579597/2000000000 : ℝ)|=(874579597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056855179/2500000000 : ℝ)|^8273 ≤ (31846066895383/100000000000000 : ℝ)^6225
        have hw : |(1056855179/2500000000 : ℝ)|=(1056855179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4523430941/10000000000 : ℝ)|^8273 ≤ (17421611011729/50000000000000 : ℝ)^6225
        have hw : |(4523430941/10000000000 : ℝ)|=(4523430941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s4_4 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2195892587/10000000000 : ℝ)*x 0 + (262743533/500000000 : ℝ)*x 1 + (2702304219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2195892587/10000000000 : ℝ)^8273 ≤ (13335330579191/100000000000000 : ℝ)^6225 := by
    have hnat : (2195892587 : ℕ)^8273*100000000000000^6225 ≤ 13335330579191^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195892587 10000000000 13335330579191 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262743533/500000000 : ℝ)^8273 ≤ (21261703908169/50000000000000 : ℝ)^6225 := by
    have hnat : (262743533 : ℕ)^8273*50000000000000^6225 ≤ 21261703908169^6225*500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262743533 500000000 21261703908169 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702304219/5000000000 : ℝ)^8273 ≤ (11035315397919/25000000000000 : ℝ)^6225 := by
    have hnat : (2702304219 : ℕ)^8273*25000000000000^6225 ≤ 11035315397919^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702304219 5000000000 11035315397919 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2195892587/10000000000 : ℝ), (262743533/500000000 : ℝ), (2702304219/5000000000 : ℝ)] ![(13335330579191/100000000000000 : ℝ), (21261703908169/50000000000000 : ℝ), (11035315397919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2195892587/10000000000 : ℝ)|^8273 ≤ (13335330579191/100000000000000 : ℝ)^6225
        have hw : |(-2195892587/10000000000 : ℝ)|=(2195892587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262743533/500000000 : ℝ)|^8273 ≤ (21261703908169/50000000000000 : ℝ)^6225
        have hw : |(262743533/500000000 : ℝ)|=(262743533/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702304219/5000000000 : ℝ)|^8273 ≤ (11035315397919/25000000000000 : ℝ)^6225
        have hw : |(2702304219/5000000000 : ℝ)|=(2702304219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s4_5 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327424029/2500000000 : ℝ)*x 0 + (-1061151331/5000000000 : ℝ)*x 1 + (2702304263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327424029/2500000000 : ℝ)^8273 ≤ (1077850926361/2500000000000 : ℝ)^6225 := by
    have hnat : (1327424029 : ℕ)^8273*2500000000000^6225 ≤ 1077850926361^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327424029 2500000000 1077850926361 2500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061151331/5000000000 : ℝ)^8273 ≤ (39827188719/312500000000 : ℝ)^6225 := by
    have hnat : (1061151331 : ℕ)^8273*312500000000^6225 ≤ 39827188719^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061151331 5000000000 39827188719 312500000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702304263/5000000000 : ℝ)^8273 ≤ (2207063127343/5000000000000 : ℝ)^6225 := by
    have hnat : (2702304263 : ℕ)^8273*5000000000000^6225 ≤ 2207063127343^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702304263 5000000000 2207063127343 5000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327424029/2500000000 : ℝ), (-1061151331/5000000000 : ℝ), (2702304263/5000000000 : ℝ)] ![(1077850926361/2500000000000 : ℝ), (39827188719/312500000000 : ℝ), (2207063127343/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327424029/2500000000 : ℝ)|^8273 ≤ (1077850926361/2500000000000 : ℝ)^6225
        have hw : |(1327424029/2500000000 : ℝ)|=(1327424029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1061151331/5000000000 : ℝ)|^8273 ≤ (39827188719/312500000000 : ℝ)^6225
        have hw : |(-1061151331/5000000000 : ℝ)|=(1061151331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702304263/5000000000 : ℝ)|^8273 ≤ (2207063127343/5000000000000 : ℝ)^6225
        have hw : |(2702304263/5000000000 : ℝ)|=(2702304263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s4_6 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309696019/10000000000 : ℝ)*x 0 + (2702304187/5000000000 : ℝ)*x 1 + (-2122303/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309696019/10000000000 : ℝ)^8273 ≤ (21557018003843/50000000000000 : ℝ)^6225 := by
    have hnat : (5309696019 : ℕ)^8273*50000000000000^6225 ≤ 21557018003843^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309696019 10000000000 21557018003843 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702304187/5000000000 : ℝ)^8273 ≤ (44141260896997/100000000000000 : ℝ)^6225 := by
    have hnat : (2702304187 : ℕ)^8273*100000000000000^6225 ≤ 44141260896997^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702304187 5000000000 44141260896997 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122303/10000000 : ℝ)^8273 ≤ (12744703087587/100000000000000 : ℝ)^6225 := by
    have hnat : (2122303 : ℕ)^8273*100000000000000^6225 ≤ 12744703087587^6225*10000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122303 10000000 12744703087587 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309696019/10000000000 : ℝ), (2702304187/5000000000 : ℝ), (-2122303/10000000 : ℝ)] ![(21557018003843/50000000000000 : ℝ), (44141260896997/100000000000000 : ℝ), (12744703087587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309696019/10000000000 : ℝ)|^8273 ≤ (21557018003843/50000000000000 : ℝ)^6225
        have hw : |(5309696019/10000000000 : ℝ)|=(5309696019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702304187/5000000000 : ℝ)|^8273 ≤ (44141260896997/100000000000000 : ℝ)^6225
        have hw : |(2702304187/5000000000 : ℝ)|=(2702304187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2122303/10000000 : ℝ)|^8273 ≤ (12744703087587/100000000000000 : ℝ)^6225
        have hw : |(-2122303/10000000 : ℝ)|=(2122303/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s4_7 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (8745827/20000000 : ℝ)*x 0 + (1130642017/2500000000 : ℝ)*x 1 + (4228287273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8745827/20000000 : ℝ)^8273 ≤ (16655434062569/50000000000000 : ℝ)^6225 := by
    have hnat : (8745827 : ℕ)^8273*50000000000000^6225 ≤ 16655434062569^6225*20000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8745827 20000000 16655434062569 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130642017/2500000000 : ℝ)^8273 ≤ (34834389043119/100000000000000 : ℝ)^6225 := by
    have hnat : (1130642017 : ℕ)^8273*100000000000000^6225 ≤ 34834389043119^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130642017 2500000000 34834389043119 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228287273/10000000000 : ℝ)^8273 ≤ (31854742820171/100000000000000 : ℝ)^6225 := by
    have hnat : (4228287273 : ℕ)^8273*100000000000000^6225 ≤ 31854742820171^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228287273 10000000000 31854742820171 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8745827/20000000 : ℝ), (1130642017/2500000000 : ℝ), (4228287273/10000000000 : ℝ)] ![(16655434062569/50000000000000 : ℝ), (34834389043119/100000000000000 : ℝ), (31854742820171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8745827/20000000 : ℝ)|^8273 ≤ (16655434062569/50000000000000 : ℝ)^6225
        have hw : |(8745827/20000000 : ℝ)|=(8745827/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130642017/2500000000 : ℝ)|^8273 ≤ (34834389043119/100000000000000 : ℝ)^6225
        have hw : |(1130642017/2500000000 : ℝ)|=(1130642017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228287273/10000000000 : ℝ)|^8273 ≤ (31854742820171/100000000000000 : ℝ)^6225
        have hw : |(4228287273/10000000000 : ℝ)|=(4228287273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1080_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7443/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5221/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2763/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14241/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7443/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5221/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7443/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5221/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7443/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5221/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7443/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5221/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7443/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5221/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7443/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5221/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5221/50000 : ℝ) ^ (517/128 : ℝ) ≤ (10884437585683391/100000000000000000000 : ℝ) := by
    have hpowers : (5221/50000 : ℝ)^517 ≤ (10884437585683391/100000000000000000000 : ℝ)^128 := by
      have hnat : (5221 : ℕ)^517*100000000000000000000^128 ≤ 10884437585683391^128*50000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5221 50000 10884437585683391 100000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5221/50000 : ℝ)) (X := (10884437585683391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hpowhi : (7443/50000 : ℝ) ^ (517/128 : ℝ) ≤ (9116511737996319/20000000000000000000 : ℝ) := by
    have hpowers : (7443/50000 : ℝ)^517 ≤ (9116511737996319/20000000000000000000 : ℝ)^128 := by
      have hnat : (7443 : ℕ)^517*20000000000000000000^128 ≤ 9116511737996319^128*50000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7443 50000 9116511737996319 20000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7443/50000 : ℝ)) (X := (9116511737996319/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010884437585683391/50000000000000000000 : ℝ) ≤ (10000538914478411/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (50010884437585683391/50000000000000000000 : ℝ)^128 ≤ (10000538914478411/10000000000000000 : ℝ)^517 := by
      have hnat : (50010884437585683391 : ℕ)^128*10000000000000000^517 ≤ 10000538914478411^517*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010884437585683391 50000000000000000000 10000538914478411 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538914478411/10000000000000000 : ℝ)) (X := (50010884437585683391/50000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50028233498137832493/50000000000000000000 : ℝ) ≤ (10001397725455563/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (50028233498137832493/50000000000000000000 : ℝ)^128 ≤ (10001397725455563/10000000000000000 : ℝ)^517 := by
      have hnat : (50028233498137832493 : ℕ)^128*10000000000000000^517 ≤ 10001397725455563^517*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028233498137832493 50000000000000000000 10001397725455563 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001397725455563/10000000000000000 : ℝ)) (X := (50028233498137832493/50000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (10009116511737996319/10000000000000000000 : ℝ) ≤ (2000451307286543/2000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (10009116511737996319/10000000000000000000 : ℝ)^128 ≤ (2000451307286543/2000000000000000 : ℝ)^517 := by
      have hnat : (10009116511737996319 : ℕ)^128*2000000000000000^517 ≤ 2000451307286543^517*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10009116511737996319 10000000000000000000 2000451307286543 2000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000451307286543/2000000000000000 : ℝ)) (X := (10009116511737996319/10000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10884437585683391/100000000000000000000 : ℝ) ≤ ((11106114881873804029/11110000000000000000 : ℝ)+2*(6709460759/3471875000000 : ℝ)*(5221/50000 : ℝ))^(517/128 : ℝ) := by
    rw [show (11106114881873804029/11110000000000000000 : ℝ)+2*(6709460759/3471875000000 : ℝ)*(5221/50000 : ℝ)=(10000538914478411/10000000000000000 : ℝ) by norm_num, show 1+2*(10884437585683391/100000000000000000000 : ℝ)=(50010884437585683391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9116511737996319/20000000000000000000 : ℝ)+(10884437585683391/100000000000000000000 : ℝ) ≤ ((11106114881873804029/11110000000000000000 : ℝ)+(6709460759/3471875000000 : ℝ)*((7443/50000 : ℝ)+(5221/50000 : ℝ)))^(517/128 : ℝ) := by
    rw [show (11106114881873804029/11110000000000000000 : ℝ)+(6709460759/3471875000000 : ℝ)*((7443/50000 : ℝ)+(5221/50000 : ℝ))=(10001397725455563/10000000000000000 : ℝ) by norm_num, show 1+(9116511737996319/20000000000000000000 : ℝ)+(10884437585683391/100000000000000000000 : ℝ)=(50028233498137832493/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9116511737996319/20000000000000000000 : ℝ) ≤ ((11106114881873804029/11110000000000000000 : ℝ)+2*(6709460759/3471875000000 : ℝ)*(7443/50000 : ℝ))^(517/128 : ℝ) := by
    rw [show (11106114881873804029/11110000000000000000 : ℝ)+2*(6709460759/3471875000000 : ℝ)*(7443/50000 : ℝ)=(2000451307286543/2000000000000000 : ℝ) by norm_num, show 1+2*(9116511737996319/20000000000000000000 : ℝ)=(10009116511737996319/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11106114881873804029/11110000000000000000 : ℝ)*(X 1 0+X 2 0)+(6709460759/3471875000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (5221/50000 : ℝ)) (hi := (7443/50000 : ℝ)) (c := (11106114881873804029/11110000000000000000 : ℝ)) (alpha := (6709460759/3471875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11106114881873804029/11110000000000000000 : ℝ)*(X 0 1+X 2 1)+(6709460759/3471875000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (5221/50000 : ℝ)) (hi := (7443/50000 : ℝ)) (c := (11106114881873804029/11110000000000000000 : ℝ)) (alpha := (6709460759/3471875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11106114881873804029/11110000000000000000 : ℝ)*(X 0 2+X 1 2)+(6709460759/3471875000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (5221/50000 : ℝ)) (hi := (7443/50000 : ℝ)) (c := (11106114881873804029/11110000000000000000 : ℝ)) (alpha := (6709460759/3471875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-109794221/500000000 : ℝ)*X 0 0+(1081009873/2000000000 : ℝ)*X 0 1+(1050886351/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534767341/1000000000 : ℝ)*X 1 0+(-284060019/1250000000 : ℝ)*X 1 1+(5254431589/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347673523/10000000000 : ℝ)*X 2 0+(1313607903/2500000000 : ℝ)*X 2 1+(-2272479971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874579597/2000000000 : ℝ)*X 0 0+(1056855179/2500000000 : ℝ)*X 0 1+(4523430941/10000000000 : ℝ)*X 0 2+(874579597/2000000000 : ℝ)*X 1 0+(1056855179/2500000000 : ℝ)*X 1 1+(4523430941/10000000000 : ℝ)*X 1 2+(874579597/2000000000 : ℝ)*X 2 0+(1056855179/2500000000 : ℝ)*X 2 1+(4523430941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2195892587/10000000000 : ℝ)*X 0 0+(262743533/500000000 : ℝ)*X 0 1+(2702304219/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327424029/2500000000 : ℝ)*X 1 0+(-1061151331/5000000000 : ℝ)*X 1 1+(2702304263/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309696019/10000000000 : ℝ)*X 2 0+(2702304187/5000000000 : ℝ)*X 2 1+(-2122303/10000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((8745827/20000000 : ℝ)*X 0 0+(1130642017/2500000000 : ℝ)*X 0 1+(4228287273/10000000000 : ℝ)*X 0 2+(8745827/20000000 : ℝ)*X 1 0+(1130642017/2500000000 : ℝ)*X 1 1+(4228287273/10000000000 : ℝ)*X 1 2+(8745827/20000000 : ℝ)*X 2 0+(1130642017/2500000000 : ℝ)*X 2 1+(4228287273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1345152247119937088649542049/277750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (135758691/50000000000000 : ℝ)*(base19) + (41832511/100000000000000 : ℝ)*(base23) + (270539737/100000000000000 : ℝ)*(lower2) + (72687381/100000000000000 : ℝ)*(lower4) + (355353/6250000000000 : ℝ)*(lower5) + (5008793616988873/100000000000000 : ℝ)*(major0) + (5008793616988873/100000000000000 : ℝ)*(major1) + (5008793616988873/100000000000000 : ℝ)*(major2) + (829915659768413/12500000000000 : ℝ)*(sp0) + (1659831561918861/25000000000000 : ℝ)*(sp1) + (1327865295472063/20000000000000 : ℝ)*(sp2) + (675651974084531/20000000000000 : ℝ)*(sp3) + (620522761/50000000000000 : ℝ)*(sp4) + (682927843/100000000000000 : ℝ)*(sp7) + (1689130276675249/50000000000000 : ℝ)*(f.failure) + (3319663259596413/50000000000000 : ℝ)*(f.sum) + (1442985124969/5555000000000000000000000000 : ℝ)*base65 + (11828965508793969317/1111000000000000000000000000000000 : ℝ)*base67 + (8943610888667969317/1111000000000000000000000000000000 : ℝ)*base69 + (13967318395452969317/1111000000000000000000000000000000 : ℝ)*base71 + (14823875767/173593750000000000000000000 : ℝ)*base73 + (971672328292030683/1111000000000000000000000000000000 : ℝ)*base76 + (3670908467197969317/1111000000000000000000000000000000 : ℝ)*base77 + (15932520334493969317/1111000000000000000000000000000000 : ℝ)*base79 + (32548885068329/5555000000000000000000000000 : ℝ)*base81 + (16524981/2500000000000000000000 : ℝ)*base90 + (16524981/2500000000000000000000 : ℝ)*base92 + (16524981/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136076892078164773430061177/22220000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (215860447/12500000000000 : ℝ)*(base19) + (369946579/20000000000000 : ℝ)*(base23) + (49059389/100000000000000 : ℝ)*(upper3) + (43095561/25000000000000 : ℝ)*(lower4) + (134142689/100000000000000 : ℝ)*(upper5) + (201529003309071/4000000000000 : ℝ)*(major0) + (201529003309071/4000000000000 : ℝ)*(major1) + (201529003309071/4000000000000 : ℝ)*(major2) + (53488945453/100000000000000 : ℝ)*(sp1) + (42331223543/100000000000000 : ℝ)*(sp2) + (6678338887596001/100000000000000 : ℝ)*(sp4) + (1669570917941743/25000000000000 : ℝ)*(sp5) + (1669573676659891/25000000000000 : ℝ)*(sp6) + (53095485526903/1562500000000 : ℝ)*(sp7) + (53095485526903/1562500000000 : ℝ)*(f.failure) + (6678338887596001/100000000000000 : ℝ)*(f.sum) + (354929693603/1111000000000000000000000000 : ℝ)*base66 + (20733322365807059/44440000000000000000000000000000 : ℝ)*base67 + (121369849806912941/44440000000000000000000000000000 : ℝ)*base70 + (21746155916767059/44440000000000000000000000000000 : ℝ)*base71 + (53573367873/8679687500000000000000000 : ℝ)*base73 + (226153221577352941/44440000000000000000000000000000 : ℝ)*base76 + (196012609273352941/44440000000000000000000000000000 : ℝ)*base78 + (707359176302672941/44440000000000000000000000000000 : ℝ)*base80 + (2716922479347/1111000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (393343/78125000000000000000 : ℝ)*base89 + (393343/78125000000000000000 : ℝ)*base91 + (393343/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1080_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7443/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5221/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2763/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1080_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1080_s5_0 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-549168407/2500000000 : ℝ)*x 0 + (337287431/625000000 : ℝ)*x 1 + (5262364681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549168407/2500000000 : ℝ)^8273 ≤ (2668326914089/20000000000000 : ℝ)^6225 := by
    have hnat : (549168407 : ℕ)^8273*20000000000000^6225 ≤ 2668326914089^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549168407 2500000000 2668326914089 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337287431/625000000 : ℝ)^8273 ≤ (44054344349831/100000000000000 : ℝ)^6225 := by
    have hnat : (337287431 : ℕ)^8273*100000000000000^6225 ≤ 44054344349831^6225*625000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337287431 625000000 44054344349831 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262364681/10000000000 : ℝ)^8273 ≤ (42604021068551/100000000000000 : ℝ)^6225 := by
    have hnat : (5262364681 : ℕ)^8273*100000000000000^6225 ≤ 42604021068551^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262364681 10000000000 42604021068551 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549168407/2500000000 : ℝ), (337287431/625000000 : ℝ), (5262364681/10000000000 : ℝ)] ![(2668326914089/20000000000000 : ℝ), (44054344349831/100000000000000 : ℝ), (42604021068551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549168407/2500000000 : ℝ)|^8273 ≤ (2668326914089/20000000000000 : ℝ)^6225
        have hw : |(-549168407/2500000000 : ℝ)|=(549168407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337287431/625000000 : ℝ)|^8273 ≤ (44054344349831/100000000000000 : ℝ)^6225
        have hw : |(337287431/625000000 : ℝ)|=(337287431/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262364681/10000000000 : ℝ)|^8273 ≤ (42604021068551/100000000000000 : ℝ)^6225
        have hw : |(5262364681/10000000000 : ℝ)|=(5262364681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s5_1 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345567197/10000000000 : ℝ)*x 0 + (-2264813289/10000000000 : ℝ)*x 1 + (1315590943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345567197/10000000000 : ℝ)^8273 ≤ (43501561228339/100000000000000 : ℝ)^6225 := by
    have hnat : (5345567197 : ℕ)^8273*100000000000000^6225 ≤ 43501561228339^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345567197 10000000000 43501561228339 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264813289/10000000000 : ℝ)^8273 ≤ (1736803433427/12500000000000 : ℝ)^6225 := by
    have hnat : (2264813289 : ℕ)^8273*12500000000000^6225 ≤ 1736803433427^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264813289 10000000000 1736803433427 12500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315590943/2500000000 : ℝ)^8273 ≤ (42604011288139/100000000000000 : ℝ)^6225 := by
    have hnat : (1315590943 : ℕ)^8273*100000000000000^6225 ≤ 42604011288139^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315590943 2500000000 42604011288139 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345567197/10000000000 : ℝ), (-2264813289/10000000000 : ℝ), (1315590943/2500000000 : ℝ)] ![(43501561228339/100000000000000 : ℝ), (1736803433427/12500000000000 : ℝ), (42604011288139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345567197/10000000000 : ℝ)|^8273 ≤ (43501561228339/100000000000000 : ℝ)^6225
        have hw : |(5345567197/10000000000 : ℝ)|=(5345567197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2264813289/10000000000 : ℝ)|^8273 ≤ (1736803433427/12500000000000 : ℝ)^6225
        have hw : |(-2264813289/10000000000 : ℝ)|=(2264813289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315590943/2500000000 : ℝ)|^8273 ≤ (42604011288139/100000000000000 : ℝ)^6225
        have hw : |(1315590943/2500000000 : ℝ)|=(1315590943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s5_2 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672783567/5000000000 : ℝ)*x 0 + (42098917/80000000 : ℝ)*x 1 + (-1132406123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672783567/5000000000 : ℝ)^8273 ≤ (43501560546981/100000000000000 : ℝ)^6225 := by
    have hnat : (2672783567 : ℕ)^8273*100000000000000^6225 ≤ 43501560546981^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672783567 5000000000 43501560546981 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42098917/80000000 : ℝ)^8273 ≤ (21302010233009/50000000000000 : ℝ)^6225 := by
    have hnat : (42098917 : ℕ)^8273*50000000000000^6225 ≤ 21302010233009^6225*80000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42098917 80000000 21302010233009 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132406123/5000000000 : ℝ)^8273 ≤ (6947209481777/50000000000000 : ℝ)^6225 := by
    have hnat : (1132406123 : ℕ)^8273*50000000000000^6225 ≤ 6947209481777^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132406123 5000000000 6947209481777 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672783567/5000000000 : ℝ), (42098917/80000000 : ℝ), (-1132406123/5000000000 : ℝ)] ![(43501560546981/100000000000000 : ℝ), (21302010233009/50000000000000 : ℝ), (6947209481777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672783567/5000000000 : ℝ)|^8273 ≤ (43501560546981/100000000000000 : ℝ)^6225
        have hw : |(2672783567/5000000000 : ℝ)|=(2672783567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42098917/80000000 : ℝ)|^8273 ≤ (21302010233009/50000000000000 : ℝ)^6225
        have hw : |(42098917/80000000 : ℝ)|=(42098917/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1132406123/5000000000 : ℝ)|^8273 ≤ (6947209481777/50000000000000 : ℝ)^6225
        have hw : |(-1132406123/5000000000 : ℝ)|=(1132406123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s5_3 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136667419/312500000 : ℝ)*x 0 + (1060864919/2500000000 : ℝ)*x 1 + (4507271531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136667419/312500000 : ℝ)^8273 ≤ (33315362186073/100000000000000 : ℝ)^6225 := by
    have hnat : (136667419 : ℕ)^8273*100000000000000^6225 ≤ 33315362186073^6225*312500000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136667419 312500000 33315362186073 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060864919/2500000000 : ℝ)^8273 ≤ (16003371434131/50000000000000 : ℝ)^6225 := by
    have hnat : (1060864919 : ℕ)^8273*50000000000000^6225 ≤ 16003371434131^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060864919 2500000000 16003371434131 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507271531/10000000000 : ℝ)^8273 ≤ (34677894933899/100000000000000 : ℝ)^6225 := by
    have hnat : (4507271531 : ℕ)^8273*100000000000000^6225 ≤ 34677894933899^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507271531 10000000000 34677894933899 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136667419/312500000 : ℝ), (1060864919/2500000000 : ℝ), (4507271531/10000000000 : ℝ)] ![(33315362186073/100000000000000 : ℝ), (16003371434131/50000000000000 : ℝ), (34677894933899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136667419/312500000 : ℝ)|^8273 ≤ (33315362186073/100000000000000 : ℝ)^6225
        have hw : |(136667419/312500000 : ℝ)|=(136667419/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060864919/2500000000 : ℝ)|^8273 ≤ (16003371434131/50000000000000 : ℝ)^6225
        have hw : |(1060864919/2500000000 : ℝ)|=(1060864919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507271531/10000000000 : ℝ)|^8273 ≤ (34677894933899/100000000000000 : ℝ)^6225
        have hw : |(4507271531/10000000000 : ℝ)|=(4507271531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s5_4 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098339673/5000000000 : ℝ)*x 0 + (5262713419/10000000000 : ℝ)*x 1 + (215849951/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098339673/5000000000 : ℝ)^8273 ≤ (533667228987/4000000000000 : ℝ)^6225 := by
    have hnat : (1098339673 : ℕ)^8273*4000000000000^6225 ≤ 533667228987^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098339673 5000000000 533667228987 4000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262713419/10000000000 : ℝ)^8273 ≤ (42607773366577/100000000000000 : ℝ)^6225 := by
    have hnat : (5262713419 : ℕ)^8273*100000000000000^6225 ≤ 42607773366577^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262713419 10000000000 42607773366577 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215849951/400000000 : ℝ)^8273 ≤ (44050545905239/100000000000000 : ℝ)^6225 := by
    have hnat : (215849951 : ℕ)^8273*100000000000000^6225 ≤ 44050545905239^6225*400000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215849951 400000000 44050545905239 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098339673/5000000000 : ℝ), (5262713419/10000000000 : ℝ), (215849951/400000000 : ℝ)] ![(533667228987/4000000000000 : ℝ), (42607773366577/100000000000000 : ℝ), (44050545905239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098339673/5000000000 : ℝ)|^8273 ≤ (533667228987/4000000000000 : ℝ)^6225
        have hw : |(-1098339673/5000000000 : ℝ)|=(1098339673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262713419/10000000000 : ℝ)|^8273 ≤ (42607773366577/100000000000000 : ℝ)^6225
        have hw : |(5262713419/10000000000 : ℝ)|=(5262713419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215849951/400000000 : ℝ)|^8273 ≤ (44050545905239/100000000000000 : ℝ)^6225
        have hw : |(215849951/400000000 : ℝ)|=(215849951/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s5_5 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (41497803/78125000 : ℝ)*x 0 + (-532732161/2500000000 : ℝ)*x 1 + (5396248771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41497803/78125000 : ℝ)^8273 ≤ (2156793279267/5000000000000 : ℝ)^6225 := by
    have hnat : (41497803 : ℕ)^8273*5000000000000^6225 ≤ 2156793279267^6225*78125000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41497803 78125000 2156793279267 5000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532732161/2500000000 : ℝ)^8273 ≤ (12813588541919/100000000000000 : ℝ)^6225 := by
    have hnat : (532732161 : ℕ)^8273*100000000000000^6225 ≤ 12813588541919^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532732161 2500000000 12813588541919 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396248771/10000000000 : ℝ)^8273 ≤ (11012636465461/25000000000000 : ℝ)^6225 := by
    have hnat : (5396248771 : ℕ)^8273*25000000000000^6225 ≤ 11012636465461^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396248771 10000000000 11012636465461 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41497803/78125000 : ℝ), (-532732161/2500000000 : ℝ), (5396248771/10000000000 : ℝ)] ![(2156793279267/5000000000000 : ℝ), (12813588541919/100000000000000 : ℝ), (11012636465461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41497803/78125000 : ℝ)|^8273 ≤ (2156793279267/5000000000000 : ℝ)^6225
        have hw : |(41497803/78125000 : ℝ)|=(41497803/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-532732161/2500000000 : ℝ)|^8273 ≤ (12813588541919/100000000000000 : ℝ)^6225
        have hw : |(-532732161/2500000000 : ℝ)|=(532732161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396248771/10000000000 : ℝ)|^8273 ≤ (11012636465461/25000000000000 : ℝ)^6225
        have hw : |(5396248771/10000000000 : ℝ)|=(5396248771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s5_6 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311718787/10000000000 : ℝ)*x 0 + (5396248769/10000000000 : ℝ)*x 1 + (-1065464321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311718787/10000000000 : ℝ)^8273 ≤ (21567932808859/50000000000000 : ℝ)^6225 := by
    have hnat : (5311718787 : ℕ)^8273*50000000000000^6225 ≤ 21567932808859^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311718787 10000000000 21567932808859 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396248769/10000000000 : ℝ)^8273 ≤ (22025272920073/50000000000000 : ℝ)^6225 := by
    have hnat : (5396248769 : ℕ)^8273*50000000000000^6225 ≤ 22025272920073^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396248769 10000000000 22025272920073 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065464321/5000000000 : ℝ)^8273 ≤ (12813588525937/100000000000000 : ℝ)^6225 := by
    have hnat : (1065464321 : ℕ)^8273*100000000000000^6225 ≤ 12813588525937^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065464321 5000000000 12813588525937 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311718787/10000000000 : ℝ), (5396248769/10000000000 : ℝ), (-1065464321/5000000000 : ℝ)] ![(21567932808859/50000000000000 : ℝ), (22025272920073/50000000000000 : ℝ), (12813588525937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311718787/10000000000 : ℝ)|^8273 ≤ (21567932808859/50000000000000 : ℝ)^6225
        have hw : |(5311718787/10000000000 : ℝ)|=(5311718787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396248769/10000000000 : ℝ)|^8273 ≤ (22025272920073/50000000000000 : ℝ)^6225
        have hw : |(5396248769/10000000000 : ℝ)|=(5396248769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065464321/5000000000 : ℝ)|^8273 ≤ (12813588525937/100000000000000 : ℝ)^6225
        have hw : |(-1065464321/5000000000 : ℝ)|=(1065464321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s5_7 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186684143/5000000000 : ℝ)*x 0 + (901317219/2000000000 : ℝ)*x 1 + (2122073913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186684143/5000000000 : ℝ)^8273 ≤ (33315472315269/100000000000000 : ℝ)^6225 := by
    have hnat : (2186684143 : ℕ)^8273*100000000000000^6225 ≤ 33315472315269^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186684143 5000000000 33315472315269 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901317219/2000000000 : ℝ)^8273 ≤ (34670886536517/100000000000000 : ℝ)^6225 := by
    have hnat : (901317219 : ℕ)^8273*100000000000000^6225 ≤ 34670886536517^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901317219 2000000000 34670886536517 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122073913/5000000000 : ℝ)^8273 ≤ (4001705141449/12500000000000 : ℝ)^6225 := by
    have hnat : (2122073913 : ℕ)^8273*12500000000000^6225 ≤ 4001705141449^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122073913 5000000000 4001705141449 12500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186684143/5000000000 : ℝ), (901317219/2000000000 : ℝ), (2122073913/5000000000 : ℝ)] ![(33315472315269/100000000000000 : ℝ), (34670886536517/100000000000000 : ℝ), (4001705141449/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186684143/5000000000 : ℝ)|^8273 ≤ (33315472315269/100000000000000 : ℝ)^6225
        have hw : |(2186684143/5000000000 : ℝ)|=(2186684143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901317219/2000000000 : ℝ)|^8273 ≤ (34670886536517/100000000000000 : ℝ)^6225
        have hw : |(901317219/2000000000 : ℝ)|=(901317219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2122073913/5000000000 : ℝ)|^8273 ≤ (4001705141449/12500000000000 : ℝ)^6225
        have hw : |(2122073913/5000000000 : ℝ)|=(2122073913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1080_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2763/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11221/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (879/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2763/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2763/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2763/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2763/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2763/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2763/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2763/25000 : ℝ) ^ (517/128 : ℝ) ≤ (427807048702551/3125000000000000000 : ℝ) := by
    have hpowers : (2763/25000 : ℝ)^517 ≤ (427807048702551/3125000000000000000 : ℝ)^128 := by
      have hnat : (2763 : ℕ)^517*3125000000000000000^128 ≤ 427807048702551^128*25000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2763 25000 427807048702551 3125000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2763/25000 : ℝ)) (X := (427807048702551/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14241/100000 : ℝ) ^ (517/128 : ℝ) ≤ (9528776260874771/25000000000000000000 : ℝ) := by
    have hpowers : (14241/100000 : ℝ)^517 ≤ (9528776260874771/25000000000000000000 : ℝ)^128 := by
      have hnat : (14241 : ℕ)^517*25000000000000000000^128 ≤ 9528776260874771^128*100000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14241 100000 9528776260874771 25000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14241/100000 : ℝ)) (X := (9528776260874771/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562927807048702551/1562500000000000000 : ℝ) ≤ (10000677801626879/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (1562927807048702551/1562500000000000000 : ℝ)^128 ≤ (10000677801626879/10000000000000000 : ℝ)^517 := by
      have hnat : (1562927807048702551 : ℕ)^128*10000000000000000^517 ≤ 10000677801626879^517*1562500000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562927807048702551 1562500000000000000 10000677801626879 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000677801626879/10000000000000000 : ℝ)) (X := (1562927807048702551/1562500000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012951232650495179/25000000000000000000 : ℝ) ≤ (10001282347998993/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (25012951232650495179/25000000000000000000 : ℝ)^128 ≤ (10001282347998993/10000000000000000 : ℝ)^517 := by
      have hnat : (25012951232650495179 : ℕ)^128*10000000000000000^517 ≤ 10001282347998993^517*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012951232650495179 25000000000000000000 10001282347998993 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001282347998993/10000000000000000 : ℝ)) (X := (25012951232650495179/25000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509528776260874771/12500000000000000000 : ℝ) ≤ (10001886894371107/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (12509528776260874771/12500000000000000000 : ℝ)^128 ≤ (10001886894371107/10000000000000000 : ℝ)^517 := by
      have hnat : (12509528776260874771 : ℕ)^128*10000000000000000^517 ≤ 10001886894371107^517*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509528776260874771 12500000000000000000 10001886894371107 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001886894371107/10000000000000000 : ℝ)) (X := (12509528776260874771/12500000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(427807048702551/3125000000000000000 : ℝ) ≤ ((425050648218385457/425200000000000000 : ℝ)+2*(302273186057/159450000000000 : ℝ)*(2763/25000 : ℝ))^(517/128 : ℝ) := by
    rw [show (425050648218385457/425200000000000000 : ℝ)+2*(302273186057/159450000000000 : ℝ)*(2763/25000 : ℝ)=(10000677801626879/10000000000000000 : ℝ) by norm_num, show 1+2*(427807048702551/3125000000000000000 : ℝ)=(1562927807048702551/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9528776260874771/25000000000000000000 : ℝ)+(427807048702551/3125000000000000000 : ℝ) ≤ ((425050648218385457/425200000000000000 : ℝ)+(302273186057/159450000000000 : ℝ)*((14241/100000 : ℝ)+(2763/25000 : ℝ)))^(517/128 : ℝ) := by
    rw [show (425050648218385457/425200000000000000 : ℝ)+(302273186057/159450000000000 : ℝ)*((14241/100000 : ℝ)+(2763/25000 : ℝ))=(10001282347998993/10000000000000000 : ℝ) by norm_num, show 1+(9528776260874771/25000000000000000000 : ℝ)+(427807048702551/3125000000000000000 : ℝ)=(25012951232650495179/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9528776260874771/25000000000000000000 : ℝ) ≤ ((425050648218385457/425200000000000000 : ℝ)+2*(302273186057/159450000000000 : ℝ)*(14241/100000 : ℝ))^(517/128 : ℝ) := by
    rw [show (425050648218385457/425200000000000000 : ℝ)+2*(302273186057/159450000000000 : ℝ)*(14241/100000 : ℝ)=(10001886894371107/10000000000000000 : ℝ) by norm_num, show 1+2*(9528776260874771/25000000000000000000 : ℝ)=(12509528776260874771/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (425050648218385457/425200000000000000 : ℝ)*(X 1 0+X 2 0)+(302273186057/159450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (2763/25000 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (425050648218385457/425200000000000000 : ℝ)) (alpha := (302273186057/159450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (425050648218385457/425200000000000000 : ℝ)*(X 0 1+X 2 1)+(302273186057/159450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (2763/25000 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (425050648218385457/425200000000000000 : ℝ)) (alpha := (302273186057/159450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (425050648218385457/425200000000000000 : ℝ)*(X 0 2+X 1 2)+(302273186057/159450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (2763/25000 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (425050648218385457/425200000000000000 : ℝ)) (alpha := (302273186057/159450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-549168407/2500000000 : ℝ)*X 0 0+(337287431/625000000 : ℝ)*X 0 1+(5262364681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345567197/10000000000 : ℝ)*X 1 0+(-2264813289/10000000000 : ℝ)*X 1 1+(1315590943/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672783567/5000000000 : ℝ)*X 2 0+(42098917/80000000 : ℝ)*X 2 1+(-1132406123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((136667419/312500000 : ℝ)*X 0 0+(1060864919/2500000000 : ℝ)*X 0 1+(4507271531/10000000000 : ℝ)*X 0 2+(136667419/312500000 : ℝ)*X 1 0+(1060864919/2500000000 : ℝ)*X 1 1+(4507271531/10000000000 : ℝ)*X 1 2+(136667419/312500000 : ℝ)*X 2 0+(1060864919/2500000000 : ℝ)*X 2 1+(4507271531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1098339673/5000000000 : ℝ)*X 0 0+(5262713419/10000000000 : ℝ)*X 0 1+(215849951/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41497803/78125000 : ℝ)*X 1 0+(-532732161/2500000000 : ℝ)*X 1 1+(5396248771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311718787/10000000000 : ℝ)*X 2 0+(5396248769/10000000000 : ℝ)*X 2 1+(-1065464321/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2186684143/5000000000 : ℝ)*X 0 0+(901317219/2000000000 : ℝ)*X 0 1+(2122073913/5000000000 : ℝ)*X 0 2+(2186684143/5000000000 : ℝ)*X 1 0+(901317219/2000000000 : ℝ)*X 1 1+(2122073913/5000000000 : ℝ)*X 1 2+(2186684143/5000000000 : ℝ)*X 2 0+(901317219/2000000000 : ℝ)*X 2 1+(2122073913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27689891603809028730142711/21260000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (154840901/10000000000000 : ℝ)*(base19) + (1519452077/100000000000000 : ℝ)*(base23) + (1428743/1000000000000 : ℝ)*(lower2) + (8425221/25000000000000 : ℝ)*(upper5) + (5620201838254541/100000000000000 : ℝ)*(major0) + (5620201838254541/100000000000000 : ℝ)*(major1) + (5620201838254541/100000000000000 : ℝ)*(major2) + (3724856680481583/50000000000000 : ℝ)*(sp0) + (931214503148937/12500000000000 : ℝ)*(sp1) + (931220944615121/12500000000000 : ℝ)*(sp2) + (947651605394811/25000000000000 : ℝ)*(sp3) + (55715409879/100000000000000 : ℝ)*(sp4) + (51502772539/100000000000000 : ℝ)*(sp5) + (28135142093/100000000000000 : ℝ)*(sp7) + (473829319590167/12500000000000 : ℝ)*(f.failure) + (1489953815274609/20000000000000 : ℝ)*(f.sum) + (23672593051957/7972500000000000000000000000 : ℝ)*base65 + (867688088474433289/127560000000000000000000000000000 : ℝ)*base68 + (559065685037846711/127560000000000000000000000000000 : ℝ)*base69 + (1056048111096753289/127560000000000000000000000000000 : ℝ)*base72 + (28428763296781/15945000000000000000000000000 : ℝ)*base74 + (398552008389753289/127560000000000000000000000000000 : ℝ)*base76 + (139235466657806711/127560000000000000000000000000000 : ℝ)*base77 + (3354243992314713289/127560000000000000000000000000000 : ℝ)*base80 + (10036701635089/3986250000000000000000000000 : ℝ)*base82 + (793923/625000000000000000000 : ℝ)*base90 + (793923/625000000000000000000 : ℝ)*base92 + (793923/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20861807426810149104093/2657500000000000000000000000 : ℝ) := by norm_num
    linear_combination (733012917/50000000000000 : ℝ)*(base19) + (9943483/625000000000 : ℝ)*(base23) + (157962799/100000000000000 : ℝ)*(upper3) + (27239213/50000000000000 : ℝ)*(lower4) + (160179033/100000000000000 : ℝ)*(upper5) + (5649535964046513/100000000000000 : ℝ)*(major0) + (5649535964046513/100000000000000 : ℝ)*(major1) + (5649535964046513/100000000000000 : ℝ)*(major2) + (9597108849/25000000000000 : ℝ)*(sp1) + (8247009061/20000000000000 : ℝ)*(sp2) + (1872163060450919/25000000000000 : ℝ)*(sp4) + (7488612387342447/100000000000000 : ℝ)*(sp5) + (1872152353950273/25000000000000 : ℝ)*(sp6) + (1905209712308627/50000000000000 : ℝ)*(sp7) + (1905209712308627/50000000000000 : ℝ)*(f.failure) + (1872163060450919/25000000000000 : ℝ)*(f.sum) + (3433402273063/2657500000000000000000000000 : ℝ)*base66 + (132920167206257441/42520000000000000000000000000000 : ℝ)*base67 + (73167860174657441/42520000000000000000000000000000 : ℝ)*base69 + (177675667686657441/42520000000000000000000000000000 : ℝ)*base71 + (2166786020397/664375000000000000000000000 : ℝ)*base74 + (217977611596822559/42520000000000000000000000000000 : ℝ)*base76 + (241520160244622559/42520000000000000000000000000000 : ℝ)*base78 + (152366205038822559/42520000000000000000000000000000 : ℝ)*base80 + (2412669774789/1328750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9370337/2500000000000000000000 : ℝ)*base89 + (9370337/2500000000000000000000 : ℝ)*base91 + (9370337/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1080_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2763/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (879/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1080_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1080_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3339/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (439/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (879/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1080_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1080_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1080_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3339/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (439/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (879/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1080_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
