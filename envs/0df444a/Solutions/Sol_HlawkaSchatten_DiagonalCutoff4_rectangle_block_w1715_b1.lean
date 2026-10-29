-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1715_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:54:48.122991+00:00
-- url     : https://prove2.me/submissions/90454144-d4cf-4cbd-8598-a14692486d57

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
theorem support_rectangle_w1715_s3_0 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1394214799/10000000000 : ℝ)*x 0 + (2733423527/5000000000 : ℝ)*x 1 + (2569446499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1394214799/10000000000 : ℝ)^5343 ≤ (2184727022113/25000000000000 : ℝ)^4319 := by
    have hnat : (1394214799 : ℕ)^5343*25000000000000^4319 ≤ 2184727022113^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394214799 10000000000 2184727022113 25000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733423527/5000000000 : ℝ)^5343 ≤ (23687895147073/50000000000000 : ℝ)^4319 := by
    have hnat : (2733423527 : ℕ)^5343*50000000000000^4319 ≤ 23687895147073^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733423527 5000000000 23687895147073 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569446499/5000000000 : ℝ)^5343 ≤ (548566270097/1250000000000 : ℝ)^4319 := by
    have hnat : (2569446499 : ℕ)^5343*1250000000000^4319 ≤ 548566270097^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569446499 5000000000 548566270097 1250000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1394214799/10000000000 : ℝ), (2733423527/5000000000 : ℝ), (2569446499/5000000000 : ℝ)] ![(2184727022113/25000000000000 : ℝ), (23687895147073/50000000000000 : ℝ), (548566270097/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1394214799/10000000000 : ℝ)|^5343 ≤ (2184727022113/25000000000000 : ℝ)^4319
        have hw : |(-1394214799/10000000000 : ℝ)|=(1394214799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733423527/5000000000 : ℝ)|^5343 ≤ (23687895147073/50000000000000 : ℝ)^4319
        have hw : |(2733423527/5000000000 : ℝ)|=(2733423527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569446499/5000000000 : ℝ)|^5343 ≤ (548566270097/1250000000000 : ℝ)^4319
        have hw : |(2569446499/5000000000 : ℝ)|=(2569446499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s3_1 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5341835841/10000000000 : ℝ)*x 0 + (-312839553/2000000000 : ℝ)*x 1 + (1027778601/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5341835841/10000000000 : ℝ)^5343 ≤ (46039241985467/100000000000000 : ℝ)^4319 := by
    have hnat : (5341835841 : ℕ)^5343*100000000000000^4319 ≤ 46039241985467^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341835841 10000000000 46039241985467 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312839553/2000000000 : ℝ)^5343 ≤ (5037728158339/50000000000000 : ℝ)^4319 := by
    have hnat : (312839553 : ℕ)^5343*50000000000000^4319 ≤ 5037728158339^4319*2000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312839553 2000000000 5037728158339 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027778601/2000000000 : ℝ)^5343 ≤ (2742831355107/6250000000000 : ℝ)^4319 := by
    have hnat : (1027778601 : ℕ)^5343*6250000000000^4319 ≤ 2742831355107^4319*2000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027778601 2000000000 2742831355107 6250000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5341835841/10000000000 : ℝ), (-312839553/2000000000 : ℝ), (1027778601/2000000000 : ℝ)] ![(46039241985467/100000000000000 : ℝ), (5037728158339/50000000000000 : ℝ), (2742831355107/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5341835841/10000000000 : ℝ)|^5343 ≤ (46039241985467/100000000000000 : ℝ)^4319
        have hw : |(5341835841/10000000000 : ℝ)|=(5341835841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-312839553/2000000000 : ℝ)|^5343 ≤ (5037728158339/50000000000000 : ℝ)^4319
        have hw : |(-312839553/2000000000 : ℝ)|=(312839553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027778601/2000000000 : ℝ)|^5343 ≤ (2742831355107/6250000000000 : ℝ)^4319
        have hw : |(1027778601/2000000000 : ℝ)|=(1027778601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s3_2 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1335458961/2500000000 : ℝ)*x 0 + (1027778601/2000000000 : ℝ)*x 1 + (-1564197761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335458961/2500000000 : ℝ)^5343 ≤ (46039242017453/100000000000000 : ℝ)^4319 := by
    have hnat : (1335458961 : ℕ)^5343*100000000000000^4319 ≤ 46039242017453^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335458961 2500000000 46039242017453 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027778601/2000000000 : ℝ)^5343 ≤ (2742831355107/6250000000000 : ℝ)^4319 := by
    have hnat : (1027778601 : ℕ)^5343*6250000000000^4319 ≤ 2742831355107^4319*2000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027778601 2000000000 2742831355107 6250000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1564197761/10000000000 : ℝ)^5343 ≤ (2518864071201/25000000000000 : ℝ)^4319 := by
    have hnat : (1564197761 : ℕ)^5343*25000000000000^4319 ≤ 2518864071201^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564197761 10000000000 2518864071201 25000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1335458961/2500000000 : ℝ), (1027778601/2000000000 : ℝ), (-1564197761/10000000000 : ℝ)] ![(46039242017453/100000000000000 : ℝ), (2742831355107/6250000000000 : ℝ), (2518864071201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1335458961/2500000000 : ℝ)|^5343 ≤ (46039242017453/100000000000000 : ℝ)^4319
        have hw : |(1335458961/2500000000 : ℝ)|=(1335458961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027778601/2000000000 : ℝ)|^5343 ≤ (2742831355107/6250000000000 : ℝ)^4319
        have hw : |(1027778601/2000000000 : ℝ)|=(1027778601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1564197761/10000000000 : ℝ)|^5343 ≤ (2518864071201/25000000000000 : ℝ)^4319
        have hw : |(-1564197761/10000000000 : ℝ)|=(1564197761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s3_3 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (512292573/1250000000 : ℝ)*x 0 + (3635118379/10000000000 : ℝ)*x 1 + (2298392731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512292573/1250000000 : ℝ)^5343 ≤ (8292787819291/25000000000000 : ℝ)^4319 := by
    have hnat : (512292573 : ℕ)^5343*25000000000000^4319 ≤ 8292787819291^4319*1250000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512292573 1250000000 8292787819291 25000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3635118379/10000000000 : ℝ)^5343 ≤ (28597038485693/100000000000000 : ℝ)^4319 := by
    have hnat : (3635118379 : ℕ)^5343*100000000000000^4319 ≤ 28597038485693^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3635118379 10000000000 28597038485693 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2298392731/5000000000 : ℝ)^5343 ≤ (19115905115851/50000000000000 : ℝ)^4319 := by
    have hnat : (2298392731 : ℕ)^5343*50000000000000^4319 ≤ 19115905115851^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2298392731 5000000000 19115905115851 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(512292573/1250000000 : ℝ), (3635118379/10000000000 : ℝ), (2298392731/5000000000 : ℝ)] ![(8292787819291/25000000000000 : ℝ), (28597038485693/100000000000000 : ℝ), (19115905115851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(512292573/1250000000 : ℝ)|^5343 ≤ (8292787819291/25000000000000 : ℝ)^4319
        have hw : |(512292573/1250000000 : ℝ)|=(512292573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3635118379/10000000000 : ℝ)|^5343 ≤ (28597038485693/100000000000000 : ℝ)^4319
        have hw : |(3635118379/10000000000 : ℝ)|=(3635118379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2298392731/5000000000 : ℝ)|^5343 ≤ (19115905115851/50000000000000 : ℝ)^4319
        have hw : |(2298392731/5000000000 : ℝ)|=(2298392731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s3_4 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-697181279/5000000000 : ℝ)*x 0 + (5142540713/10000000000 : ℝ)*x 1 + (2731572489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (697181279/5000000000 : ℝ)^5343 ≤ (8740053835779/100000000000000 : ℝ)^4319 := by
    have hnat : (697181279 : ℕ)^5343*100000000000000^4319 ≤ 8740053835779^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697181279 5000000000 8740053835779 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5142540713/10000000000 : ℝ)^5343 ≤ (2196192067999/5000000000000 : ℝ)^4319 := by
    have hnat : (5142540713 : ℕ)^5343*5000000000000^4319 ≤ 2196192067999^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142540713 10000000000 2196192067999 5000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731572489/5000000000 : ℝ)^5343 ≤ (47336104783529/100000000000000 : ℝ)^4319 := by
    have hnat : (2731572489 : ℕ)^5343*100000000000000^4319 ≤ 47336104783529^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731572489 5000000000 47336104783529 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-697181279/5000000000 : ℝ), (5142540713/10000000000 : ℝ), (2731572489/5000000000 : ℝ)] ![(8740053835779/100000000000000 : ℝ), (2196192067999/5000000000000 : ℝ), (47336104783529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-697181279/5000000000 : ℝ)|^5343 ≤ (8740053835779/100000000000000 : ℝ)^4319
        have hw : |(-697181279/5000000000 : ℝ)|=(697181279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5142540713/10000000000 : ℝ)|^5343 ≤ (2196192067999/5000000000000 : ℝ)^4319
        have hw : |(5142540713/10000000000 : ℝ)|=(5142540713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731572489/5000000000 : ℝ)|^5343 ≤ (47336104783529/100000000000000 : ℝ)^4319
        have hw : |(2731572489/5000000000 : ℝ)|=(2731572489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s3_5 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313511183/2500000000 : ℝ)*x 0 + (-30998643/250000000 : ℝ)*x 1 + (2731572577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313511183/2500000000 : ℝ)^5343 ≤ (2819065156809/6250000000000 : ℝ)^4319 := by
    have hnat : (1313511183 : ℕ)^5343*6250000000000^4319 ≤ 2819065156809^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313511183 2500000000 2819065156809 6250000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30998643/250000000 : ℝ)^5343 ≤ (7558850809181/100000000000000 : ℝ)^4319 := by
    have hnat : (30998643 : ℕ)^5343*100000000000000^4319 ≤ 7558850809181^4319*250000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30998643 250000000 7558850809181 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731572577/5000000000 : ℝ)^5343 ≤ (23668053335031/50000000000000 : ℝ)^4319 := by
    have hnat : (2731572577 : ℕ)^5343*50000000000000^4319 ≤ 23668053335031^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731572577 5000000000 23668053335031 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313511183/2500000000 : ℝ), (-30998643/250000000 : ℝ), (2731572577/5000000000 : ℝ)] ![(2819065156809/6250000000000 : ℝ), (7558850809181/100000000000000 : ℝ), (23668053335031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313511183/2500000000 : ℝ)|^5343 ≤ (2819065156809/6250000000000 : ℝ)^4319
        have hw : |(1313511183/2500000000 : ℝ)|=(1313511183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30998643/250000000 : ℝ)|^5343 ≤ (7558850809181/100000000000000 : ℝ)^4319
        have hw : |(-30998643/250000000 : ℝ)|=(30998643/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731572577/5000000000 : ℝ)|^5343 ≤ (23668053335031/50000000000000 : ℝ)^4319
        have hw : |(2731572577/5000000000 : ℝ)|=(2731572577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s3_6 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254044741/10000000000 : ℝ)*x 0 + (5463145083/10000000000 : ℝ)*x 1 + (-1239945809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254044741/10000000000 : ℝ)^5343 ≤ (1804201704181/4000000000000 : ℝ)^4319 := by
    have hnat : (5254044741 : ℕ)^5343*4000000000000^4319 ≤ 1804201704181^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254044741 10000000000 1804201704181 4000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463145083/10000000000 : ℝ)^5343 ≤ (47336105909017/100000000000000 : ℝ)^4319 := by
    have hnat : (5463145083 : ℕ)^5343*100000000000000^4319 ≤ 47336105909017^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463145083 10000000000 47336105909017 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1239945809/10000000000 : ℝ)^5343 ≤ (755885148037/10000000000000 : ℝ)^4319 := by
    have hnat : (1239945809 : ℕ)^5343*10000000000000^4319 ≤ 755885148037^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239945809 10000000000 755885148037 10000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254044741/10000000000 : ℝ), (5463145083/10000000000 : ℝ), (-1239945809/10000000000 : ℝ)] ![(1804201704181/4000000000000 : ℝ), (47336105909017/100000000000000 : ℝ), (755885148037/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254044741/10000000000 : ℝ)|^5343 ≤ (1804201704181/4000000000000 : ℝ)^4319
        have hw : |(5254044741/10000000000 : ℝ)|=(5254044741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463145083/10000000000 : ℝ)|^5343 ≤ (47336105909017/100000000000000 : ℝ)^4319
        have hw : |(5463145083/10000000000 : ℝ)|=(5463145083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1239945809/10000000000 : ℝ)|^5343 ≤ (755885148037/10000000000000 : ℝ)^4319
        have hw : |(-1239945809/10000000000 : ℝ)|=(1239945809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s3_7 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4098773881/10000000000 : ℝ)*x 0 + (4586088919/10000000000 : ℝ)*x 1 + (3645974287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4098773881/10000000000 : ℝ)^5343 ≤ (33175489837019/100000000000000 : ℝ)^4319 := by
    have hnat : (4098773881 : ℕ)^5343*100000000000000^4319 ≤ 33175489837019^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4098773881 10000000000 33175489837019 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4586088919/10000000000 : ℝ)^5343 ≤ (19060892011309/50000000000000 : ℝ)^4319 := by
    have hnat : (4586088919 : ℕ)^5343*50000000000000^4319 ≤ 19060892011309^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4586088919 10000000000 19060892011309 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3645974287/10000000000 : ℝ)^5343 ≤ (1148109045349/4000000000000 : ℝ)^4319 := by
    have hnat : (3645974287 : ℕ)^5343*4000000000000^4319 ≤ 1148109045349^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3645974287 10000000000 1148109045349 4000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4098773881/10000000000 : ℝ), (4586088919/10000000000 : ℝ), (3645974287/10000000000 : ℝ)] ![(33175489837019/100000000000000 : ℝ), (19060892011309/50000000000000 : ℝ), (1148109045349/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4098773881/10000000000 : ℝ)|^5343 ≤ (33175489837019/100000000000000 : ℝ)^4319
        have hw : |(4098773881/10000000000 : ℝ)|=(4098773881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4586088919/10000000000 : ℝ)|^5343 ≤ (19060892011309/50000000000000 : ℝ)^4319
        have hw : |(4586088919/10000000000 : ℝ)|=(4586088919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3645974287/10000000000 : ℝ)|^5343 ≤ (1148109045349/4000000000000 : ℝ)^4319
        have hw : |(3645974287/10000000000 : ℝ)|=(3645974287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1715_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8533/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10049/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17057/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8533/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10041/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8533/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10041/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8533/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10041/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8533/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10041/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8533/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10041/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8533/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10041/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10041/100000 : ℝ) ^ (5335/1024 : ℝ) ≤ (629936816842987/100000000000000000000 : ℝ) := by
    have hpowers : (10041/100000 : ℝ)^5335 ≤ (629936816842987/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10041 : ℕ)^5335*100000000000000000000^1024 ≤ 629936816842987^1024*100000^5335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10041 100000 629936816842987 100000000000000000000 5335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10041/100000 : ℝ)) (X := (629936816842987/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8533/50000 : ℝ) ^ (5335/1024 : ℝ) ≤ (1997406057745113/20000000000000000000 : ℝ) := by
    have hpowers : (8533/50000 : ℝ)^5335 ≤ (1997406057745113/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8533 : ℕ)^5335*20000000000000000000^1024 ≤ 1997406057745113^1024*50000^5335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8533 50000 1997406057745113 20000000000000000000 5335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8533/50000 : ℝ)) (X := (1997406057745113/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000629936816842987/50000000000000000000 : ℝ) ≤ (2000004836378759/2000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (50000629936816842987/50000000000000000000 : ℝ)^1024 ≤ (2000004836378759/2000000000000000 : ℝ)^5335 := by
      have hnat : (50000629936816842987 : ℕ)^1024*2000000000000000^5335 ≤ 2000004836378759^5335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000629936816842987 50000000000000000000 2000004836378759 2000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000004836378759/2000000000000000 : ℝ)) (X := (50000629936816842987/50000000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12501327120888196069/12500000000000000000 : ℝ) ≤ (10000203773345703/10000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (12501327120888196069/12500000000000000000 : ℝ)^1024 ≤ (10000203773345703/10000000000000000 : ℝ)^5335 := by
      have hnat : (12501327120888196069 : ℕ)^1024*10000000000000000^5335 ≤ 10000203773345703^5335*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501327120888196069 12500000000000000000 10000203773345703 10000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000203773345703/10000000000000000 : ℝ)) (X := (12501327120888196069/12500000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10001997406057745113/10000000000000000000 : ℝ) ≤ (10000383364797611/10000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (10001997406057745113/10000000000000000000 : ℝ)^1024 ≤ (10000383364797611/10000000000000000 : ℝ)^5335 := by
      have hnat : (10001997406057745113 : ℕ)^1024*10000000000000000^5335 ≤ 10000383364797611^5335*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001997406057745113 10000000000000000000 10000383364797611 10000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000383364797611/10000000000000000 : ℝ)) (X := (10001997406057745113/10000000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(629936816842987/100000000000000000000 : ℝ) ≤ ((70246563322266693419/70250000000000000000 : ℝ)+2*(44897862977/175625000000000 : ℝ)*(10041/100000 : ℝ))^(5335/1024 : ℝ) := by
    rw [show (70246563322266693419/70250000000000000000 : ℝ)+2*(44897862977/175625000000000 : ℝ)*(10041/100000 : ℝ)=(2000004836378759/2000000000000000 : ℝ) by norm_num, show 1+2*(629936816842987/100000000000000000000 : ℝ)=(50000629936816842987/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1997406057745113/20000000000000000000 : ℝ)+(629936816842987/100000000000000000000 : ℝ) ≤ ((70246563322266693419/70250000000000000000 : ℝ)+(44897862977/175625000000000 : ℝ)*((8533/50000 : ℝ)+(10041/100000 : ℝ)))^(5335/1024 : ℝ) := by
    rw [show (70246563322266693419/70250000000000000000 : ℝ)+(44897862977/175625000000000 : ℝ)*((8533/50000 : ℝ)+(10041/100000 : ℝ))=(10000203773345703/10000000000000000 : ℝ) by norm_num, show 1+(1997406057745113/20000000000000000000 : ℝ)+(629936816842987/100000000000000000000 : ℝ)=(12501327120888196069/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1997406057745113/20000000000000000000 : ℝ) ≤ ((70246563322266693419/70250000000000000000 : ℝ)+2*(44897862977/175625000000000 : ℝ)*(8533/50000 : ℝ))^(5335/1024 : ℝ) := by
    rw [show (70246563322266693419/70250000000000000000 : ℝ)+2*(44897862977/175625000000000 : ℝ)*(8533/50000 : ℝ)=(10000383364797611/10000000000000000 : ℝ) by norm_num, show 1+2*(1997406057745113/20000000000000000000 : ℝ)=(10001997406057745113/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (70246563322266693419/70250000000000000000 : ℝ)*(X 1 0+X 2 0)+(44897862977/175625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (10041/100000 : ℝ)) (hi := (8533/50000 : ℝ)) (c := (70246563322266693419/70250000000000000000 : ℝ)) (alpha := (44897862977/175625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (70246563322266693419/70250000000000000000 : ℝ)*(X 0 1+X 2 1)+(44897862977/175625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (10041/100000 : ℝ)) (hi := (8533/50000 : ℝ)) (c := (70246563322266693419/70250000000000000000 : ℝ)) (alpha := (44897862977/175625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (70246563322266693419/70250000000000000000 : ℝ)*(X 0 2+X 1 2)+(44897862977/175625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (10041/100000 : ℝ)) (hi := (8533/50000 : ℝ)) (c := (70246563322266693419/70250000000000000000 : ℝ)) (alpha := (44897862977/175625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1394214799/10000000000 : ℝ)*X 0 0+(2733423527/5000000000 : ℝ)*X 0 1+(2569446499/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5341835841/10000000000 : ℝ)*X 1 0+(-312839553/2000000000 : ℝ)*X 1 1+(1027778601/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1335458961/2500000000 : ℝ)*X 2 0+(1027778601/2000000000 : ℝ)*X 2 1+(-1564197761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((512292573/1250000000 : ℝ)*X 0 0+(3635118379/10000000000 : ℝ)*X 0 1+(2298392731/5000000000 : ℝ)*X 0 2+(512292573/1250000000 : ℝ)*X 1 0+(3635118379/10000000000 : ℝ)*X 1 1+(2298392731/5000000000 : ℝ)*X 1 2+(512292573/1250000000 : ℝ)*X 2 0+(3635118379/10000000000 : ℝ)*X 2 1+(2298392731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-697181279/5000000000 : ℝ)*X 0 0+(5142540713/10000000000 : ℝ)*X 0 1+(2731572489/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1313511183/2500000000 : ℝ)*X 1 0+(-30998643/250000000 : ℝ)*X 1 1+(2731572577/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5254044741/10000000000 : ℝ)*X 2 0+(5463145083/10000000000 : ℝ)*X 2 1+(-1239945809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4098773881/10000000000 : ℝ)*X 0 0+(4586088919/10000000000 : ℝ)*X 0 1+(3645974287/10000000000 : ℝ)*X 0 2+(4098773881/10000000000 : ℝ)*X 1 0+(4586088919/10000000000 : ℝ)*X 1 1+(3645974287/10000000000 : ℝ)*X 1 2+(4098773881/10000000000 : ℝ)*X 2 0+(4586088919/10000000000 : ℝ)*X 2 1+(3645974287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23576182726290280603822180941/1756250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (244698633/12500000000000 : ℝ)*(base19) + (91667207/5000000000000 : ℝ)*(base23) + (16821093/25000000000000 : ℝ)*(lower2) + (16169533/5000000000000 : ℝ)*(upper3) + (1479681/625000000000 : ℝ)*(upper5) + (2044560843376813/100000000000000 : ℝ)*(major0) + (2044560843376813/100000000000000 : ℝ)*(major1) + (1022280421688407/50000000000000 : ℝ)*(major2) + (762306851165483/25000000000000 : ℝ)*(sp0) + (762311221790977/25000000000000 : ℝ)*(sp1) + (47644453303263/1562500000000 : ℝ)*(sp2) + (1039867211820441/100000000000000 : ℝ)*(sp3) + (19440091039/100000000000000 : ℝ)*(sp4) + (3591354087/50000000000000 : ℝ)*(sp7) + (207974878905723/20000000000000 : ℝ)*(f.failure) + (762311711188243/25000000000000 : ℝ)*(f.sum) + (40547310335421/17562500000000000000000000000 : ℝ)*base66 + (4392901166624506353/7025000000000000000000000000000000 : ℝ)*base68 + (25506294297155493/12500000000000000000000000000000 : ℝ)*base69 + (44513233150774506353/7025000000000000000000000000000000 : ℝ)*base72 + (129352882232033/35125000000000000000000000000 : ℝ)*base73 + (157269446477844507/12500000000000000000000000000000 : ℝ)*base76 + (66447419045465306353/7025000000000000000000000000000000 : ℝ)*base78 + (79268565012440306353/7025000000000000000000000000000000 : ℝ)*base80 + (10669269409551/8781250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (5128121/400000000000000000000 : ℝ)*base89 + (5128121/400000000000000000000 : ℝ)*base91 + (1128121/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1805613378413602288964166159/219531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15901299/1562500000000 : ℝ)*(base19) + (274404787/25000000000000 : ℝ)*(base23) + (10726163/3125000000000 : ℝ)*(lower1) + (4708883/3125000000000 : ℝ)*(upper3) + (45332893/100000000000000 : ℝ)*(lower4) + (24425139/12500000000000 : ℝ)*(upper5) + (261424744164737/12500000000000 : ℝ)*(major0) + (261424744164737/12500000000000 : ℝ)*(major1) + (261424744164737/12500000000000 : ℝ)*(major2) + (87442551/12500000000000 : ℝ)*(sp1) + (3119099637576027/100000000000000 : ℝ)*(sp4) + (779774480088121/25000000000000 : ℝ)*(sp5) + (3119098539956879/100000000000000 : ℝ)*(sp6) + (1063695994897823/100000000000000 : ℝ)*(sp7) + (1063695994897823/100000000000000 : ℝ)*(f.failure) + (3119099637576027/100000000000000 : ℝ)*(f.sum) + (82553659350943/35125000000000000000000000000 : ℝ)*base65 + (5062732117758134197/878125000000000000000000000000000 : ℝ)*base68 + (4344785037567509197/878125000000000000000000000000000 : ℝ)*base70 + (382496515457490803/878125000000000000000000000000000 : ℝ)*base71 + (135242511891557/35125000000000000000000000000 : ℝ)*base74 + (11654531268098759197/878125000000000000000000000000000 : ℝ)*base76 + (189378810676884197/878125000000000000000000000000000 : ℝ)*base78 + (4237811575214384197/878125000000000000000000000000000 : ℝ)*base80 + (33469541604659/17562500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (15634821/2000000000000000000000 : ℝ)*base89 + (15634821/2000000000000000000000 : ℝ)*base91 + (15634821/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1715_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8533/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10049/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17057/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1715_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1715_s4_0 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-278843709/2000000000 : ℝ)*x 0 + (546683309/1000000000 : ℝ)*x 1 + (5138904419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (278843709/2000000000 : ℝ)^5343 ≤ (8738937135189/100000000000000 : ℝ)^4319 := by
    have hnat : (278843709 : ℕ)^5343*100000000000000^4319 ≤ 8738937135189^4319*2000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278843709 2000000000 8738937135189 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546683309/1000000000 : ℝ)^5343 ≤ (23687820295449/50000000000000 : ℝ)^4319 := by
    have hnat : (546683309 : ℕ)^5343*50000000000000^4319 ≤ 23687820295449^4319*1000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546683309 1000000000 23687820295449 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138904419/10000000000 : ℝ)^5343 ≤ (877708445313/2000000000000 : ℝ)^4319 := by
    have hnat : (5138904419 : ℕ)^5343*2000000000000^4319 ≤ 877708445313^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138904419 10000000000 877708445313 2000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-278843709/2000000000 : ℝ), (546683309/1000000000 : ℝ), (5138904419/10000000000 : ℝ)] ![(8738937135189/100000000000000 : ℝ), (23687820295449/50000000000000 : ℝ), (877708445313/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-278843709/2000000000 : ℝ)|^5343 ≤ (8738937135189/100000000000000 : ℝ)^4319
        have hw : |(-278843709/2000000000 : ℝ)|=(278843709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546683309/1000000000 : ℝ)|^5343 ≤ (23687820295449/50000000000000 : ℝ)^4319
        have hw : |(546683309/1000000000 : ℝ)|=(546683309/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138904419/10000000000 : ℝ)|^5343 ≤ (877708445313/2000000000000 : ℝ)^4319
        have hw : |(5138904419/10000000000 : ℝ)|=(5138904419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s4_1 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2670915777/5000000000 : ℝ)*x 0 + (-1564186443/10000000000 : ℝ)*x 1 + (321181617/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2670915777/5000000000 : ℝ)^5343 ≤ (46039196277381/100000000000000 : ℝ)^4319 := by
    have hnat : (2670915777 : ℕ)^5343*100000000000000^4319 ≤ 46039196277381^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2670915777 5000000000 46039196277381 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1564186443/10000000000 : ℝ)^5343 ≤ (10075366097719/100000000000000 : ℝ)^4319 := by
    have hnat : (1564186443 : ℕ)^5343*100000000000000^4319 ≤ 10075366097719^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564186443 10000000000 10075366097719 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321181617/625000000 : ℝ)^5343 ≤ (43885437615967/100000000000000 : ℝ)^4319 := by
    have hnat : (321181617 : ℕ)^5343*100000000000000^4319 ≤ 43885437615967^4319*625000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321181617 625000000 43885437615967 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2670915777/5000000000 : ℝ), (-1564186443/10000000000 : ℝ), (321181617/625000000 : ℝ)] ![(46039196277381/100000000000000 : ℝ), (10075366097719/100000000000000 : ℝ), (43885437615967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2670915777/5000000000 : ℝ)|^5343 ≤ (46039196277381/100000000000000 : ℝ)^4319
        have hw : |(2670915777/5000000000 : ℝ)|=(2670915777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1564186443/10000000000 : ℝ)|^5343 ≤ (10075366097719/100000000000000 : ℝ)^4319
        have hw : |(-1564186443/10000000000 : ℝ)|=(1564186443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(321181617/625000000 : ℝ)|^5343 ≤ (43885437615967/100000000000000 : ℝ)^4319
        have hw : |(321181617/625000000 : ℝ)|=(321181617/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s4_2 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5341832157/10000000000 : ℝ)*x 0 + (642363097/1250000000 : ℝ)*x 1 + (-1564187089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5341832157/10000000000 : ℝ)^5343 ≤ (46039202706579/100000000000000 : ℝ)^4319 := by
    have hnat : (5341832157 : ℕ)^5343*100000000000000^4319 ≤ 46039202706579^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341832157 10000000000 46039202706579 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642363097/1250000000 : ℝ)^5343 ≤ (43885426037201/100000000000000 : ℝ)^4319 := by
    have hnat : (642363097 : ℕ)^5343*100000000000000^4319 ≤ 43885426037201^4319*1250000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642363097 1250000000 43885426037201 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1564187089/10000000000 : ℝ)^5343 ≤ (10075371245343/100000000000000 : ℝ)^4319 := by
    have hnat : (1564187089 : ℕ)^5343*100000000000000^4319 ≤ 10075371245343^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564187089 10000000000 10075371245343 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5341832157/10000000000 : ℝ), (642363097/1250000000 : ℝ), (-1564187089/10000000000 : ℝ)] ![(46039202706579/100000000000000 : ℝ), (43885426037201/100000000000000 : ℝ), (10075371245343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5341832157/10000000000 : ℝ)|^5343 ≤ (46039202706579/100000000000000 : ℝ)^4319
        have hw : |(5341832157/10000000000 : ℝ)|=(5341832157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642363097/1250000000 : ℝ)|^5343 ≤ (43885426037201/100000000000000 : ℝ)^4319
        have hw : |(642363097/1250000000 : ℝ)|=(642363097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1564187089/10000000000 : ℝ)|^5343 ≤ (10075371245343/100000000000000 : ℝ)^4319
        have hw : |(-1564187089/10000000000 : ℝ)|=(1564187089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s4_3 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1024585741/2500000000 : ℝ)*x 0 + (363515573/1000000000 : ℝ)*x 1 + (919349563/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024585741/2500000000 : ℝ)^5343 ≤ (33171175107571/100000000000000 : ℝ)^4319 := by
    have hnat : (1024585741 : ℕ)^5343*100000000000000^4319 ≤ 33171175107571^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024585741 2500000000 33171175107571 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (363515573/1000000000 : ℝ)^5343 ≤ (28597401988053/100000000000000 : ℝ)^4319 := by
    have hnat : (363515573 : ℕ)^5343*100000000000000^4319 ≤ 28597401988053^4319*1000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363515573 1000000000 28597401988053 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (919349563/2000000000 : ℝ)^5343 ≤ (9557855720651/25000000000000 : ℝ)^4319 := by
    have hnat : (919349563 : ℕ)^5343*25000000000000^4319 ≤ 9557855720651^4319*2000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919349563 2000000000 9557855720651 25000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1024585741/2500000000 : ℝ), (363515573/1000000000 : ℝ), (919349563/2000000000 : ℝ)] ![(33171175107571/100000000000000 : ℝ), (28597401988053/100000000000000 : ℝ), (9557855720651/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1024585741/2500000000 : ℝ)|^5343 ≤ (33171175107571/100000000000000 : ℝ)^4319
        have hw : |(1024585741/2500000000 : ℝ)|=(1024585741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(363515573/1000000000 : ℝ)|^5343 ≤ (28597401988053/100000000000000 : ℝ)^4319
        have hw : |(363515573/1000000000 : ℝ)|=(363515573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(919349563/2000000000 : ℝ)|^5343 ≤ (9557855720651/25000000000000 : ℝ)^4319
        have hw : |(919349563/2000000000 : ℝ)|=(919349563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s4_4 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-139436609/1000000000 : ℝ)*x 0 + (205702081/400000000 : ℝ)*x 1 + (682891409/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139436609/1000000000 : ℝ)^5343 ≤ (4370040611917/50000000000000 : ℝ)^4319 := by
    have hnat : (139436609 : ℕ)^5343*50000000000000^4319 ≤ 4370040611917^4319*1000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139436609 1000000000 4370040611917 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205702081/400000000 : ℝ)^5343 ≤ (43923960886439/100000000000000 : ℝ)^4319 := by
    have hnat : (205702081 : ℕ)^5343*100000000000000^4319 ≤ 43923960886439^4319*400000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205702081 400000000 43923960886439 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682891409/1250000000 : ℝ)^5343 ≤ (47335957869807/100000000000000 : ℝ)^4319 := by
    have hnat : (682891409 : ℕ)^5343*100000000000000^4319 ≤ 47335957869807^4319*1250000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682891409 1250000000 47335957869807 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-139436609/1000000000 : ℝ), (205702081/400000000 : ℝ), (682891409/1250000000 : ℝ)] ![(4370040611917/50000000000000 : ℝ), (43923960886439/100000000000000 : ℝ), (47335957869807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-139436609/1000000000 : ℝ)|^5343 ≤ (4370040611917/50000000000000 : ℝ)^4319
        have hw : |(-139436609/1000000000 : ℝ)|=(139436609/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205702081/400000000 : ℝ)|^5343 ≤ (43923960886439/100000000000000 : ℝ)^4319
        have hw : |(205702081/400000000 : ℝ)|=(205702081/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682891409/1250000000 : ℝ)|^5343 ≤ (47335957869807/100000000000000 : ℝ)^4319
        have hw : |(682891409/1250000000 : ℝ)|=(682891409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s4_5 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313511999/2500000000 : ℝ)*x 0 + (341445697/625000000 : ℝ)*x 1 + (-19374391/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313511999/2500000000 : ℝ)^5343 ≤ (45105077173327/100000000000000 : ℝ)^4319 := by
    have hnat : (1313511999 : ℕ)^5343*100000000000000^4319 ≤ 45105077173327^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313511999 2500000000 45105077173327 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341445697/625000000 : ℝ)^5343 ≤ (9467191316707/20000000000000 : ℝ)^4319 := by
    have hnat : (341445697 : ℕ)^5343*20000000000000^4319 ≤ 9467191316707^4319*625000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341445697 625000000 9467191316707 20000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19374391/156250000 : ℝ)^5343 ≤ (7558966223757/100000000000000 : ℝ)^4319 := by
    have hnat : (19374391 : ℕ)^5343*100000000000000^4319 ≤ 7558966223757^4319*156250000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19374391 156250000 7558966223757 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313511999/2500000000 : ℝ), (341445697/625000000 : ℝ), (-19374391/156250000 : ℝ)] ![(45105077173327/100000000000000 : ℝ), (9467191316707/20000000000000 : ℝ), (7558966223757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313511999/2500000000 : ℝ)|^5343 ≤ (45105077173327/100000000000000 : ℝ)^4319
        have hw : |(1313511999/2500000000 : ℝ)|=(1313511999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341445697/625000000 : ℝ)|^5343 ≤ (9467191316707/20000000000000 : ℝ)^4319
        have hw : |(341445697/625000000 : ℝ)|=(341445697/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19374391/156250000 : ℝ)|^5343 ≤ (7558966223757/100000000000000 : ℝ)^4319
        have hw : |(-19374391/156250000 : ℝ)|=(19374391/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s4_6 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (128086761/312500000 : ℝ)*x 0 + (229302611/500000000 : ℝ)*x 1 + (729202099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128086761/312500000 : ℝ)^5343 ≤ (33175514579209/100000000000000 : ℝ)^4319 := by
    have hnat : (128086761 : ℕ)^5343*100000000000000^4319 ≤ 33175514579209^4319*312500000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128086761 312500000 33175514579209 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229302611/500000000 : ℝ)^5343 ≤ (19060703317983/50000000000000 : ℝ)^4319 := by
    have hnat : (229302611 : ℕ)^5343*50000000000000^4319 ≤ 19060703317983^4319*500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229302611 500000000 19060703317983 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (729202099/2000000000 : ℝ)^5343 ≤ (14351539380769/50000000000000 : ℝ)^4319 := by
    have hnat : (729202099 : ℕ)^5343*50000000000000^4319 ≤ 14351539380769^4319*2000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729202099 2000000000 14351539380769 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(128086761/312500000 : ℝ), (229302611/500000000 : ℝ), (729202099/2000000000 : ℝ)] ![(33175514579209/100000000000000 : ℝ), (19060703317983/50000000000000 : ℝ), (14351539380769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(128086761/312500000 : ℝ)|^5343 ≤ (33175514579209/100000000000000 : ℝ)^4319
        have hw : |(128086761/312500000 : ℝ)|=(128086761/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229302611/500000000 : ℝ)|^5343 ≤ (19060703317983/50000000000000 : ℝ)^4319
        have hw : |(229302611/500000000 : ℝ)|=(229302611/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(729202099/2000000000 : ℝ)|^5343 ≤ (14351539380769/50000000000000 : ℝ)^4319
        have hw : |(729202099/2000000000 : ℝ)|=(729202099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1715_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10049/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (201/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17057/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10049/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10049/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10049/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10049/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10049/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10049/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10049/100000 : ℝ) ^ (5335/1024 : ℝ) ≤ (632556042085249/100000000000000000000 : ℝ) := by
    have hpowers : (10049/100000 : ℝ)^5335 ≤ (632556042085249/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10049 : ℕ)^5335*100000000000000000000^1024 ≤ 632556042085249^1024*100000^5335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10049 100000 632556042085249 100000000000000000000 5335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10049/100000 : ℝ)) (X := (632556042085249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17057/100000 : ℝ) ^ (5335/1024 : ℝ) ≤ (9959620890539551/100000000000000000000 : ℝ) := by
    have hpowers : (17057/100000 : ℝ)^5335 ≤ (9959620890539551/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17057 : ℕ)^5335*100000000000000000000^1024 ≤ 9959620890539551^1024*100000^5335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17057 100000 9959620890539551 100000000000000000000 5335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17057/100000 : ℝ)) (X := (9959620890539551/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000632556042085249/50000000000000000000 : ℝ) ≤ (5000012141219799/5000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (50000632556042085249/50000000000000000000 : ℝ)^1024 ≤ (5000012141219799/5000000000000000 : ℝ)^5335 := by
      have hnat : (50000632556042085249 : ℕ)^1024*5000000000000000^5335 ≤ 5000012141219799^5335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000632556042085249 50000000000000000000 5000012141219799 5000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000012141219799/5000000000000000 : ℝ)) (X := (50000632556042085249/50000000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (125013240221165781/125000000000000000 : ℝ) ≤ (10000203297563847/10000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (125013240221165781/125000000000000000 : ℝ)^1024 ≤ (10000203297563847/10000000000000000 : ℝ)^5335 := by
      have hnat : (125013240221165781 : ℕ)^1024*10000000000000000^5335 ≤ 10000203297563847^5335*125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125013240221165781 125000000000000000 10000203297563847 10000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000203297563847/10000000000000000 : ℝ)) (X := (125013240221165781/125000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50009959620890539551/50000000000000000000 : ℝ) ≤ (312511947271503/312500000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (50009959620890539551/50000000000000000000 : ℝ)^1024 ≤ (312511947271503/312500000000000 : ℝ)^5335 := by
      have hnat : (50009959620890539551 : ℕ)^1024*312500000000000^5335 ≤ 312511947271503^5335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009959620890539551 50000000000000000000 312511947271503 312500000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312511947271503/312500000000000 : ℝ)) (X := (50009959620890539551/50000000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(632556042085249/100000000000000000000 : ℝ) ≤ ((11679428720894924397/11680000000000000000 : ℝ)+2*(59671708083/233600000000000 : ℝ)*(10049/100000 : ℝ))^(5335/1024 : ℝ) := by
    rw [show (11679428720894924397/11680000000000000000 : ℝ)+2*(59671708083/233600000000000 : ℝ)*(10049/100000 : ℝ)=(5000012141219799/5000000000000000 : ℝ) by norm_num, show 1+2*(632556042085249/100000000000000000000 : ℝ)=(50000632556042085249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9959620890539551/100000000000000000000 : ℝ)+(632556042085249/100000000000000000000 : ℝ) ≤ ((11679428720894924397/11680000000000000000 : ℝ)+(59671708083/233600000000000 : ℝ)*((17057/100000 : ℝ)+(10049/100000 : ℝ)))^(5335/1024 : ℝ) := by
    rw [show (11679428720894924397/11680000000000000000 : ℝ)+(59671708083/233600000000000 : ℝ)*((17057/100000 : ℝ)+(10049/100000 : ℝ))=(10000203297563847/10000000000000000 : ℝ) by norm_num, show 1+(9959620890539551/100000000000000000000 : ℝ)+(632556042085249/100000000000000000000 : ℝ)=(125013240221165781/125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9959620890539551/100000000000000000000 : ℝ) ≤ ((11679428720894924397/11680000000000000000 : ℝ)+2*(59671708083/233600000000000 : ℝ)*(17057/100000 : ℝ))^(5335/1024 : ℝ) := by
    rw [show (11679428720894924397/11680000000000000000 : ℝ)+2*(59671708083/233600000000000 : ℝ)*(17057/100000 : ℝ)=(312511947271503/312500000000000 : ℝ) by norm_num, show 1+2*(9959620890539551/100000000000000000000 : ℝ)=(50009959620890539551/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11679428720894924397/11680000000000000000 : ℝ)*(X 1 0+X 2 0)+(59671708083/233600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (10049/100000 : ℝ)) (hi := (17057/100000 : ℝ)) (c := (11679428720894924397/11680000000000000000 : ℝ)) (alpha := (59671708083/233600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11679428720894924397/11680000000000000000 : ℝ)*(X 0 1+X 2 1)+(59671708083/233600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (10049/100000 : ℝ)) (hi := (17057/100000 : ℝ)) (c := (11679428720894924397/11680000000000000000 : ℝ)) (alpha := (59671708083/233600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11679428720894924397/11680000000000000000 : ℝ)*(X 0 2+X 1 2)+(59671708083/233600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (10049/100000 : ℝ)) (hi := (17057/100000 : ℝ)) (c := (11679428720894924397/11680000000000000000 : ℝ)) (alpha := (59671708083/233600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-278843709/2000000000 : ℝ)*X 0 0+(546683309/1000000000 : ℝ)*X 0 1+(5138904419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2670915777/5000000000 : ℝ)*X 1 0+(-1564186443/10000000000 : ℝ)*X 1 1+(321181617/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5341832157/10000000000 : ℝ)*X 2 0+(642363097/1250000000 : ℝ)*X 2 1+(-1564187089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1024585741/2500000000 : ℝ)*X 0 0+(363515573/1000000000 : ℝ)*X 0 1+(919349563/2000000000 : ℝ)*X 0 2+(1024585741/2500000000 : ℝ)*X 1 0+(363515573/1000000000 : ℝ)*X 1 1+(919349563/2000000000 : ℝ)*X 1 2+(1024585741/2500000000 : ℝ)*X 2 0+(363515573/1000000000 : ℝ)*X 2 1+(919349563/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-139436609/1000000000 : ℝ)*X 0 0+(205702081/400000000 : ℝ)*X 0 1+(682891409/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1313511999/2500000000 : ℝ)*X 2 0+(341445697/625000000 : ℝ)*X 2 1+(-19374391/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s4_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((128086761/312500000 : ℝ)*X 0 0+(229302611/500000000 : ℝ)*X 0 1+(729202099/2000000000 : ℝ)*X 0 2+(128086761/312500000 : ℝ)*X 1 0+(229302611/500000000 : ℝ)*X 1 1+(729202099/2000000000 : ℝ)*X 1 2+(128086761/312500000 : ℝ)*X 2 0+(229302611/500000000 : ℝ)*X 2 1+(729202099/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5001282922794167348893257/1168000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (570398067/100000000000000 : ℝ)*(base19) + (96752037/10000000000000 : ℝ)*(base23) + (42964571/100000000000000 : ℝ)*(upper2) + (16851/8000000000 : ℝ)*(upper3) + (8178863881227/400000000000 : ℝ)*(major0) + (8178863881227/400000000000 : ℝ)*(major1) + (2044715970306751/100000000000000 : ℝ)*(major2) + (381182847957043/12500000000000 : ℝ)*(sp0) + (1524738967291983/50000000000000 : ℝ)*(sp1) + (47648060336413/1562500000000 : ℝ)*(sp2) + (64996681275201/6250000000000 : ℝ)*(sp3) + (1965165711/12500000000000 : ℝ)*(sp4) + (1675931231/100000000000000 : ℝ)*(sp5) + (199765549/3125000000000 : ℝ)*(sp6) + (64997080806299/6250000000000 : ℝ)*(f.failure) + (3049478504982033/100000000000000 : ℝ)*(f.sum) + (17664248165017/23360000000000000000000000000 : ℝ)*base66 + (24088149919338281/4672000000000000000000000000000 : ℝ)*base68 + (190577980366578139/16000000000000000000000000000000 : ℝ)*base69 + (37347648111466281/4672000000000000000000000000000 : ℝ)*base72 + (17987995429863/23360000000000000000000000000 : ℝ)*base73 + (36394004913421861/16000000000000000000000000000000 : ℝ)*base76 + (33247296163674881/4672000000000000000000000000000 : ℝ)*base78 + (39440176640602881/4672000000000000000000000000000 : ℝ)*base80 + (4942180715081/1168000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1106873/125000000000000000000 : ℝ)*base89 + (1106873/125000000000000000000 : ℝ)*base91 + (143127/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1715_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10049/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (201/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17057/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1715_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1715_box_0 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079417841/10000000000 : ℝ)*x 0 + (5414596529/10000000000 : ℝ)*x 1 + (5414596607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079417841/10000000000 : ℝ)^5343 ≤ (3183733160799/50000000000000 : ℝ)^4319 := by
    have hnat : (1079417841 : ℕ)^5343*50000000000000^4319 ≤ 3183733160799^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079417841 10000000000 3183733160799 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414596529/10000000000 : ℝ)^5343 ≤ (46816266418167/100000000000000 : ℝ)^4319 := by
    have hnat : (5414596529 : ℕ)^5343*100000000000000^4319 ≤ 46816266418167^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414596529 10000000000 46816266418167 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414596607/10000000000 : ℝ)^5343 ≤ (11704066813119/25000000000000 : ℝ)^4319 := by
    have hnat : (5414596607 : ℕ)^5343*25000000000000^4319 ≤ 11704066813119^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414596607 10000000000 11704066813119 25000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079417841/10000000000 : ℝ), (5414596529/10000000000 : ℝ), (5414596607/10000000000 : ℝ)] ![(3183733160799/50000000000000 : ℝ), (46816266418167/100000000000000 : ℝ), (11704066813119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079417841/10000000000 : ℝ)|^5343 ≤ (3183733160799/50000000000000 : ℝ)^4319
        have hw : |(-1079417841/10000000000 : ℝ)|=(1079417841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414596529/10000000000 : ℝ)|^5343 ≤ (46816266418167/100000000000000 : ℝ)^4319
        have hw : |(5414596529/10000000000 : ℝ)|=(5414596529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414596607/10000000000 : ℝ)|^5343 ≤ (11704066813119/25000000000000 : ℝ)^4319
        have hw : |(5414596607/10000000000 : ℝ)|=(5414596607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_1 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225145621/10000000000 : ℝ)*x 0 + (-337111449/2500000000 : ℝ)*x 1 + (2707298281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225145621/10000000000 : ℝ)^5343 ≤ (11199582036361/25000000000000 : ℝ)^4319 := by
    have hnat : (5225145621 : ℕ)^5343*25000000000000^4319 ≤ 11199582036361^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225145621 10000000000 11199582036361 25000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337111449/2500000000 : ℝ)^5343 ≤ (262043908259/3125000000000 : ℝ)^4319 := by
    have hnat : (337111449 : ℕ)^5343*3125000000000^4319 ≤ 262043908259^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337111449 2500000000 262043908259 3125000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707298281/5000000000 : ℝ)^5343 ≤ (5852033346393/12500000000000 : ℝ)^4319 := by
    have hnat : (2707298281 : ℕ)^5343*12500000000000^4319 ≤ 5852033346393^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707298281 5000000000 5852033346393 12500000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225145621/10000000000 : ℝ), (-337111449/2500000000 : ℝ), (2707298281/5000000000 : ℝ)] ![(11199582036361/25000000000000 : ℝ), (262043908259/3125000000000 : ℝ), (5852033346393/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225145621/10000000000 : ℝ)|^5343 ≤ (11199582036361/25000000000000 : ℝ)^4319
        have hw : |(5225145621/10000000000 : ℝ)|=(5225145621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-337111449/2500000000 : ℝ)|^5343 ≤ (262043908259/3125000000000 : ℝ)^4319
        have hw : |(-337111449/2500000000 : ℝ)|=(337111449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707298281/5000000000 : ℝ)|^5343 ≤ (5852033346393/12500000000000 : ℝ)^4319
        have hw : |(2707298281/5000000000 : ℝ)|=(2707298281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_2 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225145469/10000000000 : ℝ)*x 0 + (5414596681/10000000000 : ℝ)*x 1 + (-1348445841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225145469/10000000000 : ℝ)^5343 ≤ (44798326533281/100000000000000 : ℝ)^4319 := by
    have hnat : (5225145469 : ℕ)^5343*100000000000000^4319 ≤ 44798326533281^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225145469 10000000000 44798326533281 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414596681/10000000000 : ℝ)^5343 ≤ (46816268044001/100000000000000 : ℝ)^4319 := by
    have hnat : (5414596681 : ℕ)^5343*100000000000000^4319 ≤ 46816268044001^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414596681 10000000000 46816268044001 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348445841/10000000000 : ℝ)^5343 ≤ (838540541047/10000000000000 : ℝ)^4319 := by
    have hnat : (1348445841 : ℕ)^5343*10000000000000^4319 ≤ 838540541047^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348445841 10000000000 838540541047 10000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225145469/10000000000 : ℝ), (5414596681/10000000000 : ℝ), (-1348445841/10000000000 : ℝ)] ![(44798326533281/100000000000000 : ℝ), (46816268044001/100000000000000 : ℝ), (838540541047/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225145469/10000000000 : ℝ)|^5343 ≤ (44798326533281/100000000000000 : ℝ)^4319
        have hw : |(5225145469/10000000000 : ℝ)|=(5225145469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414596681/10000000000 : ℝ)|^5343 ≤ (46816268044001/100000000000000 : ℝ)^4319
        have hw : |(5414596681/10000000000 : ℝ)|=(5414596681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1348445841/10000000000 : ℝ)|^5343 ≤ (838540541047/10000000000000 : ℝ)^4319
        have hw : |(-1348445841/10000000000 : ℝ)|=(1348445841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_3 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2239840437/5000000000 : ℝ)*x 0 + (1964536887/5000000000 : ℝ)*x 1 + (982268431/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2239840437/5000000000 : ℝ)^5343 ≤ (37030585306169/100000000000000 : ℝ)^4319 := by
    have hnat : (2239840437 : ℕ)^5343*100000000000000^4319 ≤ 37030585306169^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239840437 5000000000 37030585306169 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1964536887/5000000000 : ℝ)^5343 ≤ (31484707592597/100000000000000 : ℝ)^4319 := by
    have hnat : (1964536887 : ℕ)^5343*100000000000000^4319 ≤ 31484707592597^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964536887 5000000000 31484707592597 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (982268431/2500000000 : ℝ)^5343 ≤ (1574235354847/5000000000000 : ℝ)^4319 := by
    have hnat : (982268431 : ℕ)^5343*5000000000000^4319 ≤ 1574235354847^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982268431 2500000000 1574235354847 5000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2239840437/5000000000 : ℝ), (1964536887/5000000000 : ℝ), (982268431/2500000000 : ℝ)] ![(37030585306169/100000000000000 : ℝ), (31484707592597/100000000000000 : ℝ), (1574235354847/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2239840437/5000000000 : ℝ)|^5343 ≤ (37030585306169/100000000000000 : ℝ)^4319
        have hw : |(2239840437/5000000000 : ℝ)|=(2239840437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1964536887/5000000000 : ℝ)|^5343 ≤ (31484707592597/100000000000000 : ℝ)^4319
        have hw : |(1964536887/5000000000 : ℝ)|=(1964536887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(982268431/2500000000 : ℝ)|^5343 ≤ (1574235354847/5000000000000 : ℝ)^4319
        have hw : |(982268431/2500000000 : ℝ)|=(982268431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_4 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1729568689/10000000000 : ℝ)*x 0 + (2588835953/5000000000 : ℝ)*x 1 + (5177671917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1729568689/10000000000 : ℝ)^5343 ≤ (11409300747163/100000000000000 : ℝ)^4319 := by
    have hnat : (1729568689 : ℕ)^5343*100000000000000^4319 ≤ 11409300747163^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729568689 10000000000 11409300747163 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588835953/5000000000 : ℝ)^5343 ≤ (22147674779981/50000000000000 : ℝ)^4319 := by
    have hnat : (2588835953 : ℕ)^5343*50000000000000^4319 ≤ 22147674779981^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588835953 5000000000 22147674779981 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177671917/10000000000 : ℝ)^5343 ≤ (44295349676379/100000000000000 : ℝ)^4319 := by
    have hnat : (5177671917 : ℕ)^5343*100000000000000^4319 ≤ 44295349676379^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177671917 10000000000 44295349676379 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1729568689/10000000000 : ℝ), (2588835953/5000000000 : ℝ), (5177671917/10000000000 : ℝ)] ![(11409300747163/100000000000000 : ℝ), (22147674779981/50000000000000 : ℝ), (44295349676379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1729568689/10000000000 : ℝ)|^5343 ≤ (11409300747163/100000000000000 : ℝ)^4319
        have hw : |(-1729568689/10000000000 : ℝ)|=(1729568689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588835953/5000000000 : ℝ)|^5343 ≤ (22147674779981/50000000000000 : ℝ)^4319
        have hw : |(2588835953/5000000000 : ℝ)|=(2588835953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177671917/10000000000 : ℝ)|^5343 ≤ (44295349676379/100000000000000 : ℝ)^4319
        have hw : |(5177671917/10000000000 : ℝ)|=(5177671917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_5 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385631407/10000000000 : ℝ)*x 0 + (-181641293/1250000000 : ℝ)*x 1 + (1294417949/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385631407/10000000000 : ℝ)^5343 ≤ (23253322094159/50000000000000 : ℝ)^4319 := by
    have hnat : (5385631407 : ℕ)^5343*50000000000000^4319 ≤ 23253322094159^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385631407 10000000000 23253322094159 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181641293/1250000000 : ℝ)^5343 ≤ (1149750925273/12500000000000 : ℝ)^4319 := by
    have hnat : (181641293 : ℕ)^5343*12500000000000^4319 ≤ 1149750925273^4319*1250000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181641293 1250000000 1149750925273 12500000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294417949/2500000000 : ℝ)^5343 ≤ (44295348395787/100000000000000 : ℝ)^4319 := by
    have hnat : (1294417949 : ℕ)^5343*100000000000000^4319 ≤ 44295348395787^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294417949 2500000000 44295348395787 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385631407/10000000000 : ℝ), (-181641293/1250000000 : ℝ), (1294417949/2500000000 : ℝ)] ![(23253322094159/50000000000000 : ℝ), (1149750925273/12500000000000 : ℝ), (44295348395787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385631407/10000000000 : ℝ)|^5343 ≤ (23253322094159/50000000000000 : ℝ)^4319
        have hw : |(5385631407/10000000000 : ℝ)|=(5385631407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-181641293/1250000000 : ℝ)|^5343 ≤ (1149750925273/12500000000000 : ℝ)^4319
        have hw : |(-181641293/1250000000 : ℝ)|=(181641293/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294417949/2500000000 : ℝ)|^5343 ≤ (44295348395787/100000000000000 : ℝ)^4319
        have hw : |(1294417949/2500000000 : ℝ)|=(1294417949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_6 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385631343/10000000000 : ℝ)*x 0 + (1294417969/2500000000 : ℝ)*x 1 + (-726565161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385631343/10000000000 : ℝ)^5343 ≤ (23253321752313/50000000000000 : ℝ)^4319 := by
    have hnat : (5385631343 : ℕ)^5343*50000000000000^4319 ≤ 23253321752313^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385631343 10000000000 23253321752313 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294417969/2500000000 : ℝ)^5343 ≤ (44295349242459/100000000000000 : ℝ)^4319 := by
    have hnat : (1294417969 : ℕ)^5343*100000000000000^4319 ≤ 44295349242459^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294417969 2500000000 44295349242459 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (726565161/5000000000 : ℝ)^5343 ≤ (9198007229913/100000000000000 : ℝ)^4319 := by
    have hnat : (726565161 : ℕ)^5343*100000000000000^4319 ≤ 9198007229913^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726565161 5000000000 9198007229913 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385631343/10000000000 : ℝ), (1294417969/2500000000 : ℝ), (-726565161/5000000000 : ℝ)] ![(23253321752313/50000000000000 : ℝ), (44295349242459/100000000000000 : ℝ), (9198007229913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385631343/10000000000 : ℝ)|^5343 ≤ (23253321752313/50000000000000 : ℝ)^4319
        have hw : |(5385631343/10000000000 : ℝ)|=(5385631343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294417969/2500000000 : ℝ)|^5343 ≤ (44295349242459/100000000000000 : ℝ)^4319
        have hw : |(1294417969/2500000000 : ℝ)|=(1294417969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-726565161/5000000000 : ℝ)|^5343 ≤ (9198007229913/100000000000000 : ℝ)^4319
        have hw : |(-726565161/5000000000 : ℝ)|=(726565161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_7 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3701095019/10000000000 : ℝ)*x 0 + (134923351/312500000 : ℝ)*x 1 + (2158773519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3701095019/10000000000 : ℝ)^5343 ≤ (29240501833091/100000000000000 : ℝ)^4319 := by
    have hnat : (3701095019 : ℕ)^5343*100000000000000^4319 ≤ 29240501833091^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3701095019 10000000000 29240501833091 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134923351/312500000 : ℝ)^5343 ≤ (35379750058911/100000000000000 : ℝ)^4319 := by
    have hnat : (134923351 : ℕ)^5343*100000000000000^4319 ≤ 35379750058911^4319*312500000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134923351 312500000 35379750058911 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2158773519/5000000000 : ℝ)^5343 ≤ (35379748092287/100000000000000 : ℝ)^4319 := by
    have hnat : (2158773519 : ℕ)^5343*100000000000000^4319 ≤ 35379748092287^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158773519 5000000000 35379748092287 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3701095019/10000000000 : ℝ), (134923351/312500000 : ℝ), (2158773519/5000000000 : ℝ)] ![(29240501833091/100000000000000 : ℝ), (35379750058911/100000000000000 : ℝ), (35379748092287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3701095019/10000000000 : ℝ)|^5343 ≤ (29240501833091/100000000000000 : ℝ)^4319
        have hw : |(3701095019/10000000000 : ℝ)|=(3701095019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134923351/312500000 : ℝ)|^5343 ≤ (35379750058911/100000000000000 : ℝ)^4319
        have hw : |(134923351/312500000 : ℝ)|=(134923351/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2158773519/5000000000 : ℝ)|^5343 ≤ (35379748092287/100000000000000 : ℝ)^4319
        have hw : |(2158773519/5000000000 : ℝ)|=(2158773519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_8 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-99354133/625000000 : ℝ)*x 0 + (156329901/312500000 : ℝ)*x 1 + (1364283433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99354133/625000000 : ℝ)^5343 ≤ (10278790352403/100000000000000 : ℝ)^4319 := by
    have hnat : (99354133 : ℕ)^5343*100000000000000^4319 ≤ 10278790352403^4319*625000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99354133 625000000 10278790352403 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156329901/312500000 : ℝ)^5343 ≤ (21224765310883/50000000000000 : ℝ)^4319 := by
    have hnat : (156329901 : ℕ)^5343*50000000000000^4319 ≤ 21224765310883^4319*312500000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156329901 312500000 21224765310883 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364283433/2500000000 : ℝ)^5343 ≤ (1477239969281/3125000000000 : ℝ)^4319 := by
    have hnat : (1364283433 : ℕ)^5343*3125000000000^4319 ≤ 1477239969281^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364283433 2500000000 1477239969281 3125000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-99354133/625000000 : ℝ), (156329901/312500000 : ℝ), (1364283433/2500000000 : ℝ)] ![(10278790352403/100000000000000 : ℝ), (21224765310883/50000000000000 : ℝ), (1477239969281/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-99354133/625000000 : ℝ)|^5343 ≤ (10278790352403/100000000000000 : ℝ)^4319
        have hw : |(-99354133/625000000 : ℝ)|=(99354133/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156329901/312500000 : ℝ)|^5343 ≤ (21224765310883/50000000000000 : ℝ)^4319
        have hw : |(156329901/312500000 : ℝ)|=(156329901/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364283433/2500000000 : ℝ)|^5343 ≤ (1477239969281/3125000000000 : ℝ)^4319
        have hw : |(1364283433/2500000000 : ℝ)|=(1364283433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_9 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324771979/625000000 : ℝ)*x 0 + (-1328884757/10000000000 : ℝ)*x 1 + (1364283633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324771979/625000000 : ℝ)^5343 ≤ (1112328238779/2500000000000 : ℝ)^4319 := by
    have hnat : (324771979 : ℕ)^5343*2500000000000^4319 ≤ 1112328238779^4319*625000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324771979 625000000 1112328238779 2500000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1328884757/10000000000 : ℝ)^5343 ≤ (16470365687/200000000000 : ℝ)^4319 := by
    have hnat : (1328884757 : ℕ)^5343*200000000000^4319 ≤ 16470365687^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328884757 10000000000 16470365687 200000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364283633/2500000000 : ℝ)^5343 ≤ (9454337517981/20000000000000 : ℝ)^4319 := by
    have hnat : (1364283633 : ℕ)^5343*20000000000000^4319 ≤ 9454337517981^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364283633 2500000000 9454337517981 20000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324771979/625000000 : ℝ), (-1328884757/10000000000 : ℝ), (1364283633/2500000000 : ℝ)] ![(1112328238779/2500000000000 : ℝ), (16470365687/200000000000 : ℝ), (9454337517981/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324771979/625000000 : ℝ)|^5343 ≤ (1112328238779/2500000000000 : ℝ)^4319
        have hw : |(324771979/625000000 : ℝ)|=(324771979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1328884757/10000000000 : ℝ)|^5343 ≤ (16470365687/200000000000 : ℝ)^4319
        have hw : |(-1328884757/10000000000 : ℝ)|=(1328884757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364283633/2500000000 : ℝ)|^5343 ≤ (9454337517981/20000000000000 : ℝ)^4319
        have hw : |(1364283633/2500000000 : ℝ)|=(1364283633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_10 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299088519/2500000000 : ℝ)*x 0 + (1364283163/2500000000 : ℝ)*x 1 + (-332221013/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299088519/2500000000 : ℝ)^5343 ≤ (44493155100149/100000000000000 : ℝ)^4319 := by
    have hnat : (1299088519 : ℕ)^5343*100000000000000^4319 ≤ 44493155100149^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299088519 2500000000 44493155100149 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364283163/2500000000 : ℝ)^5343 ≤ (47271667443561/100000000000000 : ℝ)^4319 := by
    have hnat : (1364283163 : ℕ)^5343*100000000000000^4319 ≤ 47271667443561^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364283163 2500000000 47271667443561 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (332221013/2500000000 : ℝ)^5343 ≤ (8235177438733/100000000000000 : ℝ)^4319 := by
    have hnat : (332221013 : ℕ)^5343*100000000000000^4319 ≤ 8235177438733^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332221013 2500000000 8235177438733 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299088519/2500000000 : ℝ), (1364283163/2500000000 : ℝ), (-332221013/2500000000 : ℝ)] ![(44493155100149/100000000000000 : ℝ), (47271667443561/100000000000000 : ℝ), (8235177438733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299088519/2500000000 : ℝ)|^5343 ≤ (44493155100149/100000000000000 : ℝ)^4319
        have hw : |(1299088519/2500000000 : ℝ)|=(1299088519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364283163/2500000000 : ℝ)|^5343 ≤ (47271667443561/100000000000000 : ℝ)^4319
        have hw : |(1364283163/2500000000 : ℝ)|=(1364283163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-332221013/2500000000 : ℝ)|^5343 ≤ (8235177438733/100000000000000 : ℝ)^4319
        have hw : |(-332221013/2500000000 : ℝ)|=(332221013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_11 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1153623967/2500000000 : ℝ)*x 0 + (1929571797/5000000000 : ℝ)*x 1 + (771828449/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1153623967/2500000000 : ℝ)^5343 ≤ (38414115504913/100000000000000 : ℝ)^4319 := by
    have hnat : (1153623967 : ℕ)^5343*100000000000000^4319 ≤ 38414115504913^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153623967 2500000000 38414115504913 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1929571797/5000000000 : ℝ)^5343 ≤ (30792948902727/100000000000000 : ℝ)^4319 := by
    have hnat : (1929571797 : ℕ)^5343*100000000000000^4319 ≤ 30792948902727^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929571797 5000000000 30792948902727 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (771828449/2000000000 : ℝ)^5343 ≤ (30792935586713/100000000000000 : ℝ)^4319 := by
    have hnat : (771828449 : ℕ)^5343*100000000000000^4319 ≤ 30792935586713^4319*2000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771828449 2000000000 30792935586713 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1153623967/2500000000 : ℝ), (1929571797/5000000000 : ℝ), (771828449/2000000000 : ℝ)] ![(38414115504913/100000000000000 : ℝ), (30792948902727/100000000000000 : ℝ), (30792935586713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1153623967/2500000000 : ℝ)|^5343 ≤ (38414115504913/100000000000000 : ℝ)^4319
        have hw : |(1153623967/2500000000 : ℝ)|=(1153623967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1929571797/5000000000 : ℝ)|^5343 ≤ (30792948902727/100000000000000 : ℝ)^4319
        have hw : |(1929571797/5000000000 : ℝ)|=(1929571797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(771828449/2000000000 : ℝ)|^5343 ≤ (30792935586713/100000000000000 : ℝ)^4319
        have hw : |(771828449/2000000000 : ℝ)|=(771828449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_12 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-606862983/5000000000 : ℝ)*x 0 + (5581518507/10000000000 : ℝ)*x 1 + (5152604291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (606862983/5000000000 : ℝ)^5343 ≤ (7361614112853/100000000000000 : ℝ)^4319 := by
    have hnat : (606862983 : ℕ)^5343*100000000000000^4319 ≤ 7361614112853^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606862983 5000000000 7361614112853 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5581518507/10000000000 : ℝ)^5343 ≤ (24304092338329/50000000000000 : ℝ)^4319 := by
    have hnat : (5581518507 : ℕ)^5343*50000000000000^4319 ≤ 24304092338329^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5581518507 10000000000 24304092338329 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152604291/10000000000 : ℝ)^5343 ≤ (275188757463/625000000000 : ℝ)^4319 := by
    have hnat : (5152604291 : ℕ)^5343*625000000000^4319 ≤ 275188757463^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152604291 10000000000 275188757463 625000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-606862983/5000000000 : ℝ), (5581518507/10000000000 : ℝ), (5152604291/10000000000 : ℝ)] ![(7361614112853/100000000000000 : ℝ), (24304092338329/50000000000000 : ℝ), (275188757463/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-606862983/5000000000 : ℝ)|^5343 ≤ (7361614112853/100000000000000 : ℝ)^4319
        have hw : |(-606862983/5000000000 : ℝ)|=(606862983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5581518507/10000000000 : ℝ)|^5343 ≤ (24304092338329/50000000000000 : ℝ)^4319
        have hw : |(5581518507/10000000000 : ℝ)|=(5581518507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152604291/10000000000 : ℝ)|^5343 ≤ (275188757463/625000000000 : ℝ)^4319
        have hw : |(5152604291/10000000000 : ℝ)|=(5152604291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_13 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350660787/2500000000 : ℝ)*x 0 + (-365941447/2500000000 : ℝ)*x 1 + (5152603807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350660787/2500000000 : ℝ)^5343 ≤ (23344221611071/50000000000000 : ℝ)^4319 := by
    have hnat : (1350660787 : ℕ)^5343*50000000000000^4319 ≤ 23344221611071^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350660787 2500000000 23344221611071 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (365941447/2500000000 : ℝ)^5343 ≤ (4640680344163/50000000000000 : ℝ)^4319 := by
    have hnat : (365941447 : ℕ)^5343*50000000000000^4319 ≤ 4640680344163^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365941447 2500000000 4640680344163 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152603807/10000000000 : ℝ)^5343 ≤ (44030196077601/100000000000000 : ℝ)^4319 := by
    have hnat : (5152603807 : ℕ)^5343*100000000000000^4319 ≤ 44030196077601^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152603807 10000000000 44030196077601 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350660787/2500000000 : ℝ), (-365941447/2500000000 : ℝ), (5152603807/10000000000 : ℝ)] ![(23344221611071/50000000000000 : ℝ), (4640680344163/50000000000000 : ℝ), (44030196077601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350660787/2500000000 : ℝ)|^5343 ≤ (23344221611071/50000000000000 : ℝ)^4319
        have hw : |(1350660787/2500000000 : ℝ)|=(1350660787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-365941447/2500000000 : ℝ)|^5343 ≤ (4640680344163/50000000000000 : ℝ)^4319
        have hw : |(-365941447/2500000000 : ℝ)|=(365941447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152603807/10000000000 : ℝ)|^5343 ≤ (44030196077601/100000000000000 : ℝ)^4319
        have hw : |(5152603807/10000000000 : ℝ)|=(5152603807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_14 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5402643027/10000000000 : ℝ)*x 0 + (5152603793/10000000000 : ℝ)*x 1 + (-365941493/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402643027/10000000000 : ℝ)^5343 ≤ (46688441928571/100000000000000 : ℝ)^4319 := by
    have hnat : (5402643027 : ℕ)^5343*100000000000000^4319 ≤ 46688441928571^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402643027 10000000000 46688441928571 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152603793/10000000000 : ℝ)^5343 ≤ (11007548982401/25000000000000 : ℝ)^4319 := by
    have hnat : (5152603793 : ℕ)^5343*25000000000000^4319 ≤ 11007548982401^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152603793 10000000000 11007548982401 25000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365941493/2500000000 : ℝ)^5343 ≤ (9281362131637/100000000000000 : ℝ)^4319 := by
    have hnat : (365941493 : ℕ)^5343*100000000000000^4319 ≤ 9281362131637^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365941493 2500000000 9281362131637 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402643027/10000000000 : ℝ), (5152603793/10000000000 : ℝ), (-365941493/2500000000 : ℝ)] ![(46688441928571/100000000000000 : ℝ), (11007548982401/25000000000000 : ℝ), (9281362131637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402643027/10000000000 : ℝ)|^5343 ≤ (46688441928571/100000000000000 : ℝ)^4319
        have hw : |(5402643027/10000000000 : ℝ)|=(5402643027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152603793/10000000000 : ℝ)|^5343 ≤ (11007548982401/25000000000000 : ℝ)^4319
        have hw : |(5152603793/10000000000 : ℝ)|=(5152603793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-365941493/2500000000 : ℝ)|^5343 ≤ (9281362131637/100000000000000 : ℝ)^4319
        have hw : |(-365941493/2500000000 : ℝ)|=(365941493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_box_15 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1807866259/5000000000 : ℝ)*x 0 + (4358539187/10000000000 : ℝ)*x 1 + (4358537479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1807866259/5000000000 : ℝ)^5343 ≤ (14204246845817/50000000000000 : ℝ)^4319 := by
    have hnat : (1807866259 : ℕ)^5343*50000000000000^4319 ≤ 14204246845817^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1807866259 5000000000 14204246845817 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4358539187/10000000000 : ℝ)^5343 ≤ (35795761828339/100000000000000 : ℝ)^4319 := by
    have hnat : (4358539187 : ℕ)^5343*100000000000000^4319 ≤ 35795761828339^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358539187 10000000000 35795761828339 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4358537479/10000000000 : ℝ)^5343 ≤ (35795744475103/100000000000000 : ℝ)^4319 := by
    have hnat : (4358537479 : ℕ)^5343*100000000000000^4319 ≤ 35795744475103^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358537479 10000000000 35795744475103 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1807866259/5000000000 : ℝ), (4358539187/10000000000 : ℝ), (4358537479/10000000000 : ℝ)] ![(14204246845817/50000000000000 : ℝ), (35795761828339/100000000000000 : ℝ), (35795744475103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1807866259/5000000000 : ℝ)|^5343 ≤ (14204246845817/50000000000000 : ℝ)^4319
        have hw : |(1807866259/5000000000 : ℝ)|=(1807866259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4358539187/10000000000 : ℝ)|^5343 ≤ (35795761828339/100000000000000 : ℝ)^4319
        have hw : |(4358539187/10000000000 : ℝ)|=(4358539187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4358537479/10000000000 : ℝ)|^5343 ≤ (35795744475103/100000000000000 : ℝ)^4319
        have hw : |(4358537479/10000000000 : ℝ)|=(4358537479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1715_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (201/2000 : ℝ)*pair X i i ≤ pair X i h) :
    -(33397/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1463/2500 : ℝ) ∧ (40821/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (45247/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (201/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (201/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (201/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (201/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (201/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (201/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (201/2000 : ℝ) ^ (5335/1024 : ℝ) ≤ (316442031525093/50000000000000000000 : ℝ) := by
    have hpowers : (201/2000 : ℝ)^5335 ≤ (316442031525093/50000000000000000000 : ℝ)^1024 := by
      have hnat : (201 : ℕ)^5335*50000000000000000000^1024 ≤ 316442031525093^1024*2000^5335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        201 2000 316442031525093 50000000000000000000 5335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (201/2000 : ℝ)) (X := (316442031525093/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17057/100000 : ℝ) ^ (5335/1024 : ℝ) ≤ (9959620890539551/100000000000000000000 : ℝ) := by
    have hpowers : (17057/100000 : ℝ)^5335 ≤ (9959620890539551/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17057 : ℕ)^5335*100000000000000000000^1024 ≤ 9959620890539551^1024*100000^5335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17057 100000 9959620890539551 100000000000000000000 5335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17057/100000 : ℝ)) (X := (9959620890539551/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000316442031525093/25000000000000000000 : ℝ) ≤ (10000024295031539/10000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (25000316442031525093/25000000000000000000 : ℝ)^1024 ≤ (10000024295031539/10000000000000000 : ℝ)^5335 := by
      have hnat : (25000316442031525093 : ℕ)^1024*10000000000000000^5335 ≤ 10000024295031539^5335*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000316442031525093 25000000000000000000 10000024295031539 10000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000024295031539/10000000000000000 : ℝ)) (X := (25000316442031525093/25000000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100010592504953589737/100000000000000000000 : ℝ) ≤ (10000203303859343/10000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (100010592504953589737/100000000000000000000 : ℝ)^1024 ≤ (10000203303859343/10000000000000000 : ℝ)^5335 := by
      have hnat : (100010592504953589737 : ℕ)^1024*10000000000000000^5335 ≤ 10000203303859343^5335*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100010592504953589737 100000000000000000000 10000203303859343 10000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000203303859343/10000000000000000 : ℝ)) (X := (100010592504953589737/100000000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50009959620890539551/50000000000000000000 : ℝ) ≤ (10000382312687147/10000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (50009959620890539551/50000000000000000000 : ℝ)^1024 ≤ (10000382312687147/10000000000000000 : ℝ)^5335 := by
      have hnat : (50009959620890539551 : ℕ)^1024*10000000000000000^5335 ≤ 10000382312687147^5335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009959620890539551 50000000000000000000 10000382312687147 10000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000382312687147/10000000000000000 : ℝ)) (X := (50009959620890539551/50000000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(316442031525093/50000000000000000000 : ℝ) ≤ ((70066572157847133373/70070000000000000000 : ℝ)+2*(44752206951/175175000000000 : ℝ)*(201/2000 : ℝ))^(5335/1024 : ℝ) := by
    rw [show (70066572157847133373/70070000000000000000 : ℝ)+2*(44752206951/175175000000000 : ℝ)*(201/2000 : ℝ)=(10000024295031539/10000000000000000 : ℝ) by norm_num, show 1+2*(316442031525093/50000000000000000000 : ℝ)=(25000316442031525093/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9959620890539551/100000000000000000000 : ℝ)+(316442031525093/50000000000000000000 : ℝ) ≤ ((70066572157847133373/70070000000000000000 : ℝ)+(44752206951/175175000000000 : ℝ)*((17057/100000 : ℝ)+(201/2000 : ℝ)))^(5335/1024 : ℝ) := by
    rw [show (70066572157847133373/70070000000000000000 : ℝ)+(44752206951/175175000000000 : ℝ)*((17057/100000 : ℝ)+(201/2000 : ℝ))=(10000203303859343/10000000000000000 : ℝ) by norm_num, show 1+(9959620890539551/100000000000000000000 : ℝ)+(316442031525093/50000000000000000000 : ℝ)=(100010592504953589737/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9959620890539551/100000000000000000000 : ℝ) ≤ ((70066572157847133373/70070000000000000000 : ℝ)+2*(44752206951/175175000000000 : ℝ)*(17057/100000 : ℝ))^(5335/1024 : ℝ) := by
    rw [show (70066572157847133373/70070000000000000000 : ℝ)+2*(44752206951/175175000000000 : ℝ)*(17057/100000 : ℝ)=(10000382312687147/10000000000000000 : ℝ) by norm_num, show 1+2*(9959620890539551/100000000000000000000 : ℝ)=(50009959620890539551/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (70066572157847133373/70070000000000000000 : ℝ)*(X 1 0+X 2 0)+(44752206951/175175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (201/2000 : ℝ)) (hi := (17057/100000 : ℝ)) (c := (70066572157847133373/70070000000000000000 : ℝ)) (alpha := (44752206951/175175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (70066572157847133373/70070000000000000000 : ℝ)*(X 0 1+X 2 1)+(44752206951/175175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (201/2000 : ℝ)) (hi := (17057/100000 : ℝ)) (c := (70066572157847133373/70070000000000000000 : ℝ)) (alpha := (44752206951/175175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (70066572157847133373/70070000000000000000 : ℝ)*(X 0 2+X 1 2)+(44752206951/175175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (201/2000 : ℝ)) (hi := (17057/100000 : ℝ)) (c := (70066572157847133373/70070000000000000000 : ℝ)) (alpha := (44752206951/175175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1079417841/10000000000 : ℝ)*X 0 0+(5414596529/10000000000 : ℝ)*X 0 1+(5414596607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5225145621/10000000000 : ℝ)*X 1 0+(-337111449/2500000000 : ℝ)*X 1 1+(2707298281/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5225145469/10000000000 : ℝ)*X 2 0+(5414596681/10000000000 : ℝ)*X 2 1+(-1348445841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2239840437/5000000000 : ℝ)*X 0 0+(1964536887/5000000000 : ℝ)*X 0 1+(982268431/2500000000 : ℝ)*X 0 2+(2239840437/5000000000 : ℝ)*X 1 0+(1964536887/5000000000 : ℝ)*X 1 1+(982268431/2500000000 : ℝ)*X 1 2+(2239840437/5000000000 : ℝ)*X 2 0+(1964536887/5000000000 : ℝ)*X 2 1+(982268431/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1729568689/10000000000 : ℝ)*X 0 0+(2588835953/5000000000 : ℝ)*X 0 1+(5177671917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5385631407/10000000000 : ℝ)*X 1 0+(-181641293/1250000000 : ℝ)*X 1 1+(1294417949/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5385631343/10000000000 : ℝ)*X 2 0+(1294417969/2500000000 : ℝ)*X 2 1+(-726565161/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3701095019/10000000000 : ℝ)*X 0 0+(134923351/312500000 : ℝ)*X 0 1+(2158773519/5000000000 : ℝ)*X 0 2+(3701095019/10000000000 : ℝ)*X 1 0+(134923351/312500000 : ℝ)*X 1 1+(2158773519/5000000000 : ℝ)*X 1 2+(3701095019/10000000000 : ℝ)*X 2 0+(134923351/312500000 : ℝ)*X 2 1+(2158773519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-99354133/625000000 : ℝ)*X 0 0+(156329901/312500000 : ℝ)*X 0 1+(1364283433/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((324771979/625000000 : ℝ)*X 1 0+(-1328884757/10000000000 : ℝ)*X 1 1+(1364283633/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1299088519/2500000000 : ℝ)*X 2 0+(1364283163/2500000000 : ℝ)*X 2 1+(-332221013/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1153623967/2500000000 : ℝ)*X 0 0+(1929571797/5000000000 : ℝ)*X 0 1+(771828449/2000000000 : ℝ)*X 0 2+(1153623967/2500000000 : ℝ)*X 1 0+(1929571797/5000000000 : ℝ)*X 1 1+(771828449/2000000000 : ℝ)*X 1 2+(1153623967/2500000000 : ℝ)*X 2 0+(1929571797/5000000000 : ℝ)*X 2 1+(771828449/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-606862983/5000000000 : ℝ)*X 0 0+(5581518507/10000000000 : ℝ)*X 0 1+(5152604291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1350660787/2500000000 : ℝ)*X 1 0+(-365941447/2500000000 : ℝ)*X 1 1+(5152603807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5402643027/10000000000 : ℝ)*X 2 0+(5152603793/10000000000 : ℝ)*X 2 1+(-365941493/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1807866259/5000000000 : ℝ)*X 0 0+(4358539187/10000000000 : ℝ)*X 0 1+(4358537479/10000000000 : ℝ)*X 0 2+(1807866259/5000000000 : ℝ)*X 1 0+(4358539187/10000000000 : ℝ)*X 1 1+(4358537479/10000000000 : ℝ)*X 1 2+(1807866259/5000000000 : ℝ)*X 2 0+(4358539187/10000000000 : ℝ)*X 2 1+(4358537479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-33397/50000 : ℝ) ≤ (-2340037849309172999698194375515439/3503500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9067601/100000000000000 : ℝ)*(upper1) + (13527133/100000000000000 : ℝ)*(upper3) + (5007381/100000000000000 : ℝ)*(upper5) + (1369292125721719/100000000000000 : ℝ)*(major0) + (1369292125721719/100000000000000 : ℝ)*(major1) + (1369292125721719/100000000000000 : ℝ)*(major2) + (1275419907/100000000000000 : ℝ)*(sp1) + (452151683/100000000000000 : ℝ)*(sp2) + (351189/1562500000000 : ℝ)*(sp3) + (2064418860115909/100000000000000 : ℝ)*(sp4) + (64513050392683/3125000000000 : ℝ)*(sp5) + (12902615223963/625000000000 : ℝ)*(sp6) + (348214575962977/50000000000000 : ℝ)*(sp7) + (13934927/50000000000000 : ℝ)*(sp8) + (696429174402049/100000000000000 : ℝ)*(f.failure) + (2064418887985763/100000000000000 : ℝ)*(f.sum) + (95454762354519/35035000000000000000000000000 : ℝ)*base66 + (15555861327385428187/7007000000000000000000000000000000 : ℝ)*base67 + (10264987787675571813/7007000000000000000000000000000000 : ℝ)*base70 + (10188325826299571813/7007000000000000000000000000000000 : ℝ)*base72 + (2300958007277/4379375000000000000000000000 : ℝ)*base73 + (6630189508321428187/7007000000000000000000000000000000 : ℝ)*base75 + (5963294912195571813/7007000000000000000000000000000000 : ℝ)*base78 + (14092178941461571813/7007000000000000000000000000000000 : ℝ)*base80 + (132906199314321/35035000000000000000000000000 : ℝ)*base81 + (17907877/2000000000000000000000 : ℝ)*base90 + (17907877/2000000000000000000000 : ℝ)*base92 + (17907877/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (1463/2500 : ℝ) ≤ (2050319331230234414198681014029279/3503500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17581667/100000000000000 : ℝ)*(lower0) + (934957/20000000000000 : ℝ)*(upper2) + (22324327/100000000000000 : ℝ)*(lower4) + (1475553357887641/100000000000000 : ℝ)*(major0) + (1475553357887641/100000000000000 : ℝ)*(major1) + (1475553357887641/100000000000000 : ℝ)*(major2) + (1090562398258779/50000000000000 : ℝ)*(sp0) + (1090562585287389/50000000000000 : ℝ)*(sp1) + (2181124787114671/100000000000000 : ℝ)*(sp2) + (375237091322057/50000000000000 : ℝ)*(sp3) + (3002103/50000000000000 : ℝ)*(sp5) + (48683039/12500000000000 : ℝ)*(sp6) + (13121987/100000000000000 : ℝ)*(sp7) + (15202457/4000000000000 : ℝ)*(sp12) + (750474195766101/100000000000000 : ℝ)*(f.failure) + (2181125176578983/100000000000000 : ℝ)*(f.sum) + (579773339075729/35035000000000000000000000000 : ℝ)*base65 + (9464079225627256907/7007000000000000000000000000000000 : ℝ)*base68 + (35560113011449256907/7007000000000000000000000000000000 : ℝ)*base70 + (21473237740928743093/7007000000000000000000000000000000 : ℝ)*base71 + (8365597376749/2189687500000000000000000000 : ℝ)*base73 + (37837295736266256907/7007000000000000000000000000000000 : ℝ)*base76 + (109689125736216256907/7007000000000000000000000000000000 : ℝ)*base78 + (19667890399130743093/7007000000000000000000000000000000 : ℝ)*base79 + (39433103488981/35035000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (8527927/2000000000000000000000 : ℝ)*base89 + (8527927/2000000000000000000000 : ℝ)*base91 + (8527927/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40821/50000 : ℝ) ≤ (110016528811266548396884349749857/134750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13242497/25000000000000 : ℝ)*(upper0) + (714071/1250000000000 : ℝ)*(lower1) + (223013963/50000000000000 : ℝ)*(upper4) + (1493279309386539/100000000000000 : ℝ)*(major0) + (1493279309386539/100000000000000 : ℝ)*(major1) + (1493279309386539/100000000000000 : ℝ)*(major2) + (1097927289/50000000000000 : ℝ)*(sp0) + (3013852549/10000000000000 : ℝ)*(sp1) + (382735391/50000000000000 : ℝ)*(sp2) + (17076348031/50000000000000 : ℝ)*(sp3) + (1099925870954851/50000000000000 : ℝ)*(sp8) + (219982379923879/10000000000000 : ℝ)*(sp9) + (2199853172293497/100000000000000 : ℝ)*(sp10) + (759455555199243/100000000000000 : ℝ)*(sp11) + (151897941579061/20000000000000 : ℝ)*(f.failure) + (2199853937764279/100000000000000 : ℝ)*(f.sum) + (96666439692413/17517500000000000000000000000 : ℝ)*base65 + (36438752934712533953/7007000000000000000000000000000000 : ℝ)*base68 + (27434470486551533953/7007000000000000000000000000000000 : ℝ)*base70 + (5581682332354533953/7007000000000000000000000000000000 : ℝ)*base72 + (13257657470859/2189687500000000000000000000 : ℝ)*base74 + (11597087575201533953/7007000000000000000000000000000000 : ℝ)*base76 + (23825262474885466047/7007000000000000000000000000000000 : ℝ)*base77 + (58376932518032533953/7007000000000000000000000000000000 : ℝ)*base80 + (122694550058261/35035000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1850153/400000000000000000000 : ℝ)*base90 + (1850153/400000000000000000000 : ℝ)*base92 + (1850153/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-45247/50000 : ℝ) ≤ (-15851809983213330867696257031/17517500000000000000000000000 : ℝ) := by norm_num
    linear_combination (24574211/25000000000000 : ℝ)*(upper1) + (21375537/25000000000000 : ℝ)*(upper3) + (8620289/50000000000000 : ℝ)*(lower4) + (1543057991933741/100000000000000 : ℝ)*(major0) + (1543057991933741/100000000000000 : ℝ)*(major1) + (1543057991933741/100000000000000 : ℝ)*(major2) + (4549852381/100000000000000 : ℝ)*(sp4) + (44460672329/100000000000000 : ℝ)*(sp5) + (38012172543/100000000000000 : ℝ)*(sp6) + (8865988527/50000000000000 : ℝ)*(sp7) + (2331467786474877/100000000000000 : ℝ)*(sp12) + (145714242228433/6250000000000 : ℝ)*(sp13) + (466286864830943/20000000000000 : ℝ)*(sp14) + (392394837790347/50000000000000 : ℝ)*(sp15) + (196201851889437/25000000000000 : ℝ)*(f.failure) + (1165736168163629/50000000000000 : ℝ)*(f.sum) + (16365633950819/35035000000000000000000000000 : ℝ)*base65 + (46236302079634761607/7007000000000000000000000000000000 : ℝ)*base68 + (12521240246848238393/7007000000000000000000000000000000 : ℝ)*base69 + (26416866069927238393/7007000000000000000000000000000000 : ℝ)*base71 + (56887146165273/17517500000000000000000000000 : ℝ)*base74 + (74891512839476238393/7007000000000000000000000000000000 : ℝ)*base75 + (26828397150221761607/7007000000000000000000000000000000 : ℝ)*base78 + (30550276590500761607/7007000000000000000000000000000000 : ℝ)*base80 + (47836744317309/2189687500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5053199/500000000000000000000 : ℝ)*base89 + (5053199/500000000000000000000 : ℝ)*base91 + (5053199/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1715_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (201/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33397/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(1463/2500 : ℝ) else (40821/50000 : ℝ) ≤ X j i ∧ X j i ≤ (45247/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1715_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1715_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8533/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33397/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(1463/2500 : ℝ) else (40821/50000 : ℝ) ≤ X j i ∧ X j i ≤ (45247/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1715_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1715_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1715_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8533/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33397/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(1463/2500 : ℝ) else (40821/50000 : ℝ) ≤ X j i ∧ X j i ≤ (45247/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1715_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
