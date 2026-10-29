-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1697_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:43:48.051482+00:00
-- url     : https://prove2.me/submissions/9fd8ca56-0e0a-4a1a-87d9-4a65137415a3

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
theorem support_rectangle_w1697_s3_0 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-730231839/5000000000 : ℝ)*x 0 + (273925127/500000000 : ℝ)*x 1 + (5136469289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (730231839/5000000000 : ℝ)^5199 ≤ (9110996075171/100000000000000 : ℝ)^4175 := by
    have hnat : (730231839 : ℕ)^5199*100000000000000^4175 ≤ 9110996075171^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730231839 5000000000 9110996075171 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273925127/500000000 : ℝ)^5199 ≤ (23633802868181/50000000000000 : ℝ)^4175 := by
    have hnat : (273925127 : ℕ)^5199*50000000000000^4175 ≤ 23633802868181^4175*500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273925127 500000000 23633802868181 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5136469289/10000000000 : ℝ)^5199 ≤ (4362139817357/10000000000000 : ℝ)^4175 := by
    have hnat : (5136469289 : ℕ)^5199*10000000000000^4175 ≤ 4362139817357^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136469289 10000000000 4362139817357 10000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-730231839/5000000000 : ℝ), (273925127/500000000 : ℝ), (5136469289/10000000000 : ℝ)] ![(9110996075171/100000000000000 : ℝ), (23633802868181/50000000000000 : ℝ), (4362139817357/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-730231839/5000000000 : ℝ)|^5199 ≤ (9110996075171/100000000000000 : ℝ)^4175
        have hw : |(-730231839/5000000000 : ℝ)|=(730231839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273925127/500000000 : ℝ)|^5199 ≤ (23633802868181/50000000000000 : ℝ)^4175
        have hw : |(273925127/500000000 : ℝ)|=(273925127/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5136469289/10000000000 : ℝ)|^5199 ≤ (4362139817357/10000000000000 : ℝ)^4175
        have hw : |(5136469289/10000000000 : ℝ)|=(5136469289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s3_1 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347878679/10000000000 : ℝ)*x 0 + (-1638016513/10000000000 : ℝ)*x 1 + (2568234701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347878679/10000000000 : ℝ)^5199 ≤ (45868314407253/100000000000000 : ℝ)^4175 := by
    have hnat : (5347878679 : ℕ)^5199*100000000000000^4175 ≤ 45868314407253^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347878679 10000000000 45868314407253 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1638016513/10000000000 : ℝ)^5199 ≤ (1051028620629/10000000000000 : ℝ)^4175 := by
    have hnat : (1638016513 : ℕ)^5199*10000000000000^4175 ≤ 1051028620629^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1638016513 10000000000 1051028620629 10000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568234701/5000000000 : ℝ)^5199 ≤ (8724279873719/20000000000000 : ℝ)^4175 := by
    have hnat : (2568234701 : ℕ)^5199*20000000000000^4175 ≤ 8724279873719^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568234701 5000000000 8724279873719 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347878679/10000000000 : ℝ), (-1638016513/10000000000 : ℝ), (2568234701/5000000000 : ℝ)] ![(45868314407253/100000000000000 : ℝ), (1051028620629/10000000000000 : ℝ), (8724279873719/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347878679/10000000000 : ℝ)|^5199 ≤ (45868314407253/100000000000000 : ℝ)^4175
        have hw : |(5347878679/10000000000 : ℝ)|=(5347878679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1638016513/10000000000 : ℝ)|^5199 ≤ (1051028620629/10000000000000 : ℝ)^4175
        have hw : |(-1638016513/10000000000 : ℝ)|=(1638016513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568234701/5000000000 : ℝ)|^5199 ≤ (8724279873719/20000000000000 : ℝ)^4175
        have hw : |(2568234701/5000000000 : ℝ)|=(2568234701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s3_2 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347878901/10000000000 : ℝ)*x 0 + (642058643/1250000000 : ℝ)*x 1 + (-819008279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347878901/10000000000 : ℝ)^5199 ≤ (2293415838917/5000000000000 : ℝ)^4175 := by
    have hnat : (5347878901 : ℕ)^5199*5000000000000^4175 ≤ 2293415838917^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347878901 10000000000 2293415838917 5000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642058643/1250000000 : ℝ)^5199 ≤ (10905349160033/25000000000000 : ℝ)^4175 := by
    have hnat : (642058643 : ℕ)^5199*25000000000000^4175 ≤ 10905349160033^4175*1250000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642058643 1250000000 10905349160033 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (819008279/5000000000 : ℝ)^5199 ≤ (210205731317/2000000000000 : ℝ)^4175 := by
    have hnat : (819008279 : ℕ)^5199*2000000000000^4175 ≤ 210205731317^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819008279 5000000000 210205731317 2000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347878901/10000000000 : ℝ), (642058643/1250000000 : ℝ), (-819008279/5000000000 : ℝ)] ![(2293415838917/5000000000000 : ℝ), (10905349160033/25000000000000 : ℝ), (210205731317/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347878901/10000000000 : ℝ)|^5199 ≤ (2293415838917/5000000000000 : ℝ)^4175
        have hw : |(5347878901/10000000000 : ℝ)|=(5347878901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642058643/1250000000 : ℝ)|^5199 ≤ (10905349160033/25000000000000 : ℝ)^4175
        have hw : |(642058643/1250000000 : ℝ)|=(642058643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-819008279/5000000000 : ℝ)|^5199 ≤ (210205731317/2000000000000 : ℝ)^4175
        have hw : |(-819008279/5000000000 : ℝ)|=(819008279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s3_3 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4121755007/10000000000 : ℝ)*x 0 + (3659003421/10000000000 : ℝ)*x 1 + (4621284101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4121755007/10000000000 : ℝ)^5199 ≤ (3316451010901/10000000000000 : ℝ)^4175 := by
    have hnat : (4121755007 : ℕ)^5199*10000000000000^4175 ≤ 3316451010901^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4121755007 10000000000 3316451010901 10000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3659003421/10000000000 : ℝ)^5199 ≤ (28593613901079/100000000000000 : ℝ)^4175 := by
    have hnat : (3659003421 : ℕ)^5199*100000000000000^4175 ≤ 28593613901079^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3659003421 10000000000 28593613901079 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4621284101/10000000000 : ℝ)^5199 ≤ (19120937985637/50000000000000 : ℝ)^4175 := by
    have hnat : (4621284101 : ℕ)^5199*50000000000000^4175 ≤ 19120937985637^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4621284101 10000000000 19120937985637 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4121755007/10000000000 : ℝ), (3659003421/10000000000 : ℝ), (4621284101/10000000000 : ℝ)] ![(3316451010901/10000000000000 : ℝ), (28593613901079/100000000000000 : ℝ), (19120937985637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4121755007/10000000000 : ℝ)|^5199 ≤ (3316451010901/10000000000000 : ℝ)^4175
        have hw : |(4121755007/10000000000 : ℝ)|=(4121755007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3659003421/10000000000 : ℝ)|^5199 ≤ (28593613901079/100000000000000 : ℝ)^4175
        have hw : |(3659003421/10000000000 : ℝ)|=(3659003421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4621284101/10000000000 : ℝ)|^5199 ≤ (19120937985637/50000000000000 : ℝ)^4175
        have hw : |(4621284101/10000000000 : ℝ)|=(4621284101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s3_4 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1460620903/10000000000 : ℝ)*x 0 + (514021417/1000000000 : ℝ)*x 1 + (1368675517/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1460620903/10000000000 : ℝ)^5199 ≤ (9112217497271/100000000000000 : ℝ)^4175 := by
    have hnat : (1460620903 : ℕ)^5199*100000000000000^4175 ≤ 9112217497271^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460620903 10000000000 9112217497271 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514021417/1000000000 : ℝ)^5199 ≤ (8732201091593/20000000000000 : ℝ)^4175 := by
    have hnat : (514021417 : ℕ)^5199*20000000000000^4175 ≤ 8732201091593^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514021417 1000000000 8732201091593 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368675517/2500000000 : ℝ)^5199 ≤ (1475836782077/3125000000000 : ℝ)^4175 := by
    have hnat : (1368675517 : ℕ)^5199*3125000000000^4175 ≤ 1475836782077^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368675517 2500000000 1475836782077 3125000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1460620903/10000000000 : ℝ), (514021417/1000000000 : ℝ), (1368675517/2500000000 : ℝ)] ![(9112217497271/100000000000000 : ℝ), (8732201091593/20000000000000 : ℝ), (1475836782077/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1460620903/10000000000 : ℝ)|^5199 ≤ (9112217497271/100000000000000 : ℝ)^4175
        have hw : |(-1460620903/10000000000 : ℝ)|=(1460620903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(514021417/1000000000 : ℝ)|^5199 ≤ (8732201091593/20000000000000 : ℝ)^4175
        have hw : |(514021417/1000000000 : ℝ)|=(514021417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368675517/2500000000 : ℝ)|^5199 ≤ (1475836782077/3125000000000 : ℝ)^4175
        have hw : |(1368675517/2500000000 : ℝ)|=(1368675517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s3_5 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256382747/10000000000 : ℝ)*x 0 + (-259956647/2000000000 : ℝ)*x 1 + (684337759/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256382747/10000000000 : ℝ)^5199 ≤ (44893144634721/100000000000000 : ℝ)^4175 := by
    have hnat : (5256382747 : ℕ)^5199*100000000000000^4175 ≤ 44893144634721^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256382747 10000000000 44893144634721 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259956647/2000000000 : ℝ)^5199 ≤ (6156311157/78125000000 : ℝ)^4175 := by
    have hnat : (259956647 : ℕ)^5199*78125000000^4175 ≤ 6156311157^4175*2000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259956647 2000000000 6156311157 78125000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684337759/1250000000 : ℝ)^5199 ≤ (47226777069433/100000000000000 : ℝ)^4175 := by
    have hnat : (684337759 : ℕ)^5199*100000000000000^4175 ≤ 47226777069433^4175*1250000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684337759 1250000000 47226777069433 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256382747/10000000000 : ℝ), (-259956647/2000000000 : ℝ), (684337759/1250000000 : ℝ)] ![(44893144634721/100000000000000 : ℝ), (6156311157/78125000000 : ℝ), (47226777069433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256382747/10000000000 : ℝ)|^5199 ≤ (44893144634721/100000000000000 : ℝ)^4175
        have hw : |(5256382747/10000000000 : ℝ)|=(5256382747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-259956647/2000000000 : ℝ)|^5199 ≤ (6156311157/78125000000 : ℝ)^4175
        have hw : |(-259956647/2000000000 : ℝ)|=(259956647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684337759/1250000000 : ℝ)|^5199 ≤ (47226777069433/100000000000000 : ℝ)^4175
        have hw : |(684337759/1250000000 : ℝ)|=(684337759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s3_6 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256382753/10000000000 : ℝ)*x 0 + (547470207/1000000000 : ℝ)*x 1 + (-129978323/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256382753/10000000000 : ℝ)^5199 ≤ (22446572349267/50000000000000 : ℝ)^4175 := by
    have hnat : (5256382753 : ℕ)^5199*50000000000000^4175 ≤ 22446572349267^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256382753 10000000000 22446572349267 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547470207/1000000000 : ℝ)^5199 ≤ (47226777047949/100000000000000 : ℝ)^4175 := by
    have hnat : (547470207 : ℕ)^5199*100000000000000^4175 ≤ 47226777047949^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547470207 1000000000 47226777047949 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129978323/1000000000 : ℝ)^5199 ≤ (1970019560803/25000000000000 : ℝ)^4175 := by
    have hnat : (129978323 : ℕ)^5199*25000000000000^4175 ≤ 1970019560803^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129978323 1000000000 1970019560803 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256382753/10000000000 : ℝ), (547470207/1000000000 : ℝ), (-129978323/1000000000 : ℝ)] ![(22446572349267/50000000000000 : ℝ), (47226777047949/100000000000000 : ℝ), (1970019560803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256382753/10000000000 : ℝ)|^5199 ≤ (22446572349267/50000000000000 : ℝ)^4175
        have hw : |(5256382753/10000000000 : ℝ)|=(5256382753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547470207/1000000000 : ℝ)|^5199 ≤ (47226777047949/100000000000000 : ℝ)^4175
        have hw : |(547470207/1000000000 : ℝ)|=(547470207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129978323/1000000000 : ℝ)|^5199 ≤ (1970019560803/25000000000000 : ℝ)^4175
        have hw : |(-129978323/1000000000 : ℝ)|=(129978323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s3_7 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (412219881/1000000000 : ℝ)*x 0 + (4610747517/10000000000 : ℝ)*x 1 + (366969709/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412219881/1000000000 : ℝ)^5199 ≤ (33168956940967/100000000000000 : ℝ)^4175 := by
    have hnat : (412219881 : ℕ)^5199*100000000000000^4175 ≤ 33168956940967^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412219881 1000000000 33168956940967 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4610747517/10000000000 : ℝ)^5199 ≤ (38133328884423/100000000000000 : ℝ)^4175 := by
    have hnat : (4610747517 : ℕ)^5199*100000000000000^4175 ≤ 38133328884423^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4610747517 10000000000 38133328884423 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (366969709/1000000000 : ℝ)^5199 ≤ (7174428540639/25000000000000 : ℝ)^4175 := by
    have hnat : (366969709 : ℕ)^5199*25000000000000^4175 ≤ 7174428540639^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366969709 1000000000 7174428540639 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(412219881/1000000000 : ℝ), (4610747517/10000000000 : ℝ), (366969709/1000000000 : ℝ)] ![(33168956940967/100000000000000 : ℝ), (38133328884423/100000000000000 : ℝ), (7174428540639/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(412219881/1000000000 : ℝ)|^5199 ≤ (33168956940967/100000000000000 : ℝ)^4175
        have hw : |(412219881/1000000000 : ℝ)|=(412219881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4610747517/10000000000 : ℝ)|^5199 ≤ (38133328884423/100000000000000 : ℝ)^4175
        have hw : |(4610747517/10000000000 : ℝ)|=(4610747517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(366969709/1000000000 : ℝ)|^5199 ≤ (7174428540639/25000000000000 : ℝ)^4175
        have hw : |(366969709/1000000000 : ℝ)|=(366969709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1697_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17203/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9883/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4949/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8593/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17203/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9883/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17203/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9883/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17203/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9883/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17203/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9883/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17203/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9883/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17203/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9883/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9883/100000 : ℝ) ^ (5191/1024 : ℝ) ≤ (803070456245293/100000000000000000000 : ℝ) := by
    have hpowers : (9883/100000 : ℝ)^5191 ≤ (803070456245293/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9883 : ℕ)^5191*100000000000000000000^1024 ≤ 803070456245293^1024*100000^5191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9883 100000 803070456245293 100000000000000000000 5191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9883/100000 : ℝ)) (X := (803070456245293/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17203/100000 : ℝ) ^ (5191/1024 : ℝ) ≤ (6667927219949693/50000000000000000000 : ℝ) := by
    have hpowers : (17203/100000 : ℝ)^5191 ≤ (6667927219949693/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17203 : ℕ)^5191*50000000000000000000^1024 ≤ 6667927219949693^1024*100000^5191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17203 100000 6667927219949693 50000000000000000000 5191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17203/100000 : ℝ)) (X := (6667927219949693/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000803070456245293/50000000000000000000 : ℝ) ≤ (5000015841626777/5000000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (50000803070456245293/50000000000000000000 : ℝ)^1024 ≤ (5000015841626777/5000000000000000 : ℝ)^5191 := by
      have hnat : (50000803070456245293 : ℕ)^1024*5000000000000000^5191 ≤ 5000015841626777^5191*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000803070456245293 50000000000000000000 5000015841626777 5000000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000015841626777/5000000000000000 : ℝ)) (X := (50000803070456245293/50000000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100014138924896144679/100000000000000000000 : ℝ) ≤ (10000278894963119/10000000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (100014138924896144679/100000000000000000000 : ℝ)^1024 ≤ (10000278894963119/10000000000000000 : ℝ)^5191 := by
      have hnat : (100014138924896144679 : ℕ)^1024*10000000000000000^5191 ≤ 10000278894963119^5191*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100014138924896144679 100000000000000000000 10000278894963119 10000000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000278894963119/10000000000000000 : ℝ)) (X := (100014138924896144679/100000000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25006667927219949693/25000000000000000000 : ℝ) ≤ (2500131526668171/2500000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (25006667927219949693/25000000000000000000 : ℝ)^1024 ≤ (2500131526668171/2500000000000000 : ℝ)^5191 := by
      have hnat : (25006667927219949693 : ℕ)^1024*2500000000000000^5191 ≤ 2500131526668171^5191*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006667927219949693 25000000000000000000 2500131526668171 2500000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500131526668171/2500000000000000 : ℝ)) (X := (25006667927219949693/25000000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(803070456245293/100000000000000000000 : ℝ) ≤ ((7319534553476475349/7320000000000000000 : ℝ)+2*(49442341913/146400000000000 : ℝ)*(9883/100000 : ℝ))^(5191/1024 : ℝ) := by
    rw [show (7319534553476475349/7320000000000000000 : ℝ)+2*(49442341913/146400000000000 : ℝ)*(9883/100000 : ℝ)=(5000015841626777/5000000000000000 : ℝ) by norm_num, show 1+2*(803070456245293/100000000000000000000 : ℝ)=(50000803070456245293/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6667927219949693/50000000000000000000 : ℝ)+(803070456245293/100000000000000000000 : ℝ) ≤ ((7319534553476475349/7320000000000000000 : ℝ)+(49442341913/146400000000000 : ℝ)*((17203/100000 : ℝ)+(9883/100000 : ℝ)))^(5191/1024 : ℝ) := by
    rw [show (7319534553476475349/7320000000000000000 : ℝ)+(49442341913/146400000000000 : ℝ)*((17203/100000 : ℝ)+(9883/100000 : ℝ))=(10000278894963119/10000000000000000 : ℝ) by norm_num, show 1+(6667927219949693/50000000000000000000 : ℝ)+(803070456245293/100000000000000000000 : ℝ)=(100014138924896144679/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6667927219949693/50000000000000000000 : ℝ) ≤ ((7319534553476475349/7320000000000000000 : ℝ)+2*(49442341913/146400000000000 : ℝ)*(17203/100000 : ℝ))^(5191/1024 : ℝ) := by
    rw [show (7319534553476475349/7320000000000000000 : ℝ)+2*(49442341913/146400000000000 : ℝ)*(17203/100000 : ℝ)=(2500131526668171/2500000000000000 : ℝ) by norm_num, show 1+2*(6667927219949693/50000000000000000000 : ℝ)=(25006667927219949693/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7319534553476475349/7320000000000000000 : ℝ)*(X 1 0+X 2 0)+(49442341913/146400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (9883/100000 : ℝ)) (hi := (17203/100000 : ℝ)) (c := (7319534553476475349/7320000000000000000 : ℝ)) (alpha := (49442341913/146400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7319534553476475349/7320000000000000000 : ℝ)*(X 0 1+X 2 1)+(49442341913/146400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (9883/100000 : ℝ)) (hi := (17203/100000 : ℝ)) (c := (7319534553476475349/7320000000000000000 : ℝ)) (alpha := (49442341913/146400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7319534553476475349/7320000000000000000 : ℝ)*(X 0 2+X 1 2)+(49442341913/146400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (9883/100000 : ℝ)) (hi := (17203/100000 : ℝ)) (c := (7319534553476475349/7320000000000000000 : ℝ)) (alpha := (49442341913/146400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-730231839/5000000000 : ℝ)*X 0 0+(273925127/500000000 : ℝ)*X 0 1+(5136469289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347878679/10000000000 : ℝ)*X 1 0+(-1638016513/10000000000 : ℝ)*X 1 1+(2568234701/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347878901/10000000000 : ℝ)*X 2 0+(642058643/1250000000 : ℝ)*X 2 1+(-819008279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4121755007/10000000000 : ℝ)*X 0 0+(3659003421/10000000000 : ℝ)*X 0 1+(4621284101/10000000000 : ℝ)*X 0 2+(4121755007/10000000000 : ℝ)*X 1 0+(3659003421/10000000000 : ℝ)*X 1 1+(4621284101/10000000000 : ℝ)*X 1 2+(4121755007/10000000000 : ℝ)*X 2 0+(3659003421/10000000000 : ℝ)*X 2 1+(4621284101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1460620903/10000000000 : ℝ)*X 0 0+(514021417/1000000000 : ℝ)*X 0 1+(1368675517/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256382747/10000000000 : ℝ)*X 1 0+(-259956647/2000000000 : ℝ)*X 1 1+(684337759/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256382753/10000000000 : ℝ)*X 2 0+(547470207/1000000000 : ℝ)*X 2 1+(-129978323/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((412219881/1000000000 : ℝ)*X 0 0+(4610747517/10000000000 : ℝ)*X 0 1+(366969709/1000000000 : ℝ)*X 0 2+(412219881/1000000000 : ℝ)*X 1 0+(4610747517/10000000000 : ℝ)*X 1 1+(366969709/1000000000 : ℝ)*X 1 2+(412219881/1000000000 : ℝ)*X 2 0+(4610747517/10000000000 : ℝ)*X 2 1+(366969709/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (109823407325770330195459021/12200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1147683751/100000000000000 : ℝ)*(base19) + (1060979307/100000000000000 : ℝ)*(base23) + (64818517/20000000000000 : ℝ)*(upper3) + (111274801/100000000000000 : ℝ)*(upper4) + (172134121/100000000000000 : ℝ)*(upper5) + (1981457725261291/100000000000000 : ℝ)*(major0) + (1981457725261291/100000000000000 : ℝ)*(major1) + (495364431315323/25000000000000 : ℝ)*(major2) + (1461850539862831/50000000000000 : ℝ)*(sp0) + (2923707829704327/100000000000000 : ℝ)*(sp1) + (292370791640877/10000000000000 : ℝ)*(sp2) + (1039201303252063/100000000000000 : ℝ)*(sp3) + (493603901/6250000000000 : ℝ)*(sp4) + (2434909239/50000000000000 : ℝ)*(sp7) + (51960308653527/5000000000000 : ℝ)*(f.failure) + (1461854488694039/50000000000000 : ℝ)*(f.sum) + (8542703118533/4880000000000000000000000000 : ℝ)*base65 + (1811240005380928147/244000000000000000000000000000000 : ℝ)*base68 + (706005766146503409/61000000000000000000000000000000 : ℝ)*base69 + (2592635805800928147/244000000000000000000000000000000 : ℝ)*base72 + (7608246195147/4880000000000000000000000000 : ℝ)*base74 + (846718623418503409/61000000000000000000000000000000 : ℝ)*base75 + (121476517982434441/732000000000000000000000000000000 : ℝ)*base78 + (2527353462998434441/732000000000000000000000000000000 : ℝ)*base80 + (5854280697323/7320000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1434887/500000000000000000000 : ℝ)*base90 + (1434887/500000000000000000000 : ℝ)*base92 + (6434887/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (738594352039110442497976327/61000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1707086411/100000000000000 : ℝ)*(base19) + (1837554981/100000000000000 : ℝ)*(base23) + (511808793/100000000000000 : ℝ)*(lower1) + (130947259/50000000000000 : ℝ)*(upper3) + (27978883/50000000000000 : ℝ)*(lower4) + (251401367/100000000000000 : ℝ)*(upper5) + (2026132888676723/100000000000000 : ℝ)*(major0) + (2026132888676723/100000000000000 : ℝ)*(major1) + (2026132888676723/100000000000000 : ℝ)*(major2) + (1183408591/100000000000000 : ℝ)*(sp2) + (747407154935699/25000000000000 : ℝ)*(sp4) + (2919557531891/97656250000 : ℝ)*(sp5) + (373703199847403/12500000000000 : ℝ)*(sp6) + (531318377003587/50000000000000 : ℝ)*(sp7) + (531318377003587/50000000000000 : ℝ)*(f.failure) + (747407154935699/25000000000000 : ℝ)*(f.sum) + (9509656081541/7320000000000000000000000000 : ℝ)*base66 + (1878454437201448673/732000000000000000000000000000000 : ℝ)*base68 + (3257556718521448673/732000000000000000000000000000000 : ℝ)*base70 + (6500556673478551327/732000000000000000000000000000000 : ℝ)*base71 + (16893827344661/7320000000000000000000000000 : ℝ)*base74 + (1515049399161448673/732000000000000000000000000000000 : ℝ)*base76 + (3134287417101448673/732000000000000000000000000000000 : ℝ)*base78 + (244037856849448673/732000000000000000000000000000000 : ℝ)*base80 + (27288927458741/7320000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (47434253/5000000000000000000000 : ℝ)*base89 + (47434253/5000000000000000000000 : ℝ)*base91 + (47434253/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1697_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17203/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9883/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4949/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8593/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1697_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1697_s4_0 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-365118001/2500000000 : ℝ)*x 0 + (684808699/1250000000 : ℝ)*x 1 + (2568248323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (365118001/2500000000 : ℝ)^5199 ≤ (284720648623/3125000000000 : ℝ)^4175 := by
    have hnat : (365118001 : ℕ)^5199*3125000000000^4175 ≤ 284720648623^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365118001 2500000000 284720648623 3125000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684808699/1250000000 : ℝ)^5199 ≤ (9453450348813/20000000000000 : ℝ)^4175 := by
    have hnat : (684808699 : ℕ)^5199*20000000000000^4175 ≤ 9453450348813^4175*1250000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684808699 1250000000 9453450348813 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568248323/5000000000 : ℝ)^5199 ≤ (43621687485923/100000000000000 : ℝ)^4175 := by
    have hnat : (2568248323 : ℕ)^5199*100000000000000^4175 ≤ 43621687485923^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568248323 5000000000 43621687485923 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-365118001/2500000000 : ℝ), (684808699/1250000000 : ℝ), (2568248323/5000000000 : ℝ)] ![(284720648623/3125000000000 : ℝ), (9453450348813/20000000000000 : ℝ), (43621687485923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-365118001/2500000000 : ℝ)|^5199 ≤ (284720648623/3125000000000 : ℝ)^4175
        have hw : |(-365118001/2500000000 : ℝ)|=(365118001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684808699/1250000000 : ℝ)|^5199 ≤ (9453450348813/20000000000000 : ℝ)^4175
        have hw : |(684808699/1250000000 : ℝ)|=(684808699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568248323/5000000000 : ℝ)|^5199 ≤ (43621687485923/100000000000000 : ℝ)^4175
        have hw : |(2568248323/5000000000 : ℝ)|=(2568248323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s4_1 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673935813/5000000000 : ℝ)*x 0 + (-409497429/2500000000 : ℝ)*x 1 + (1284124193/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673935813/5000000000 : ℝ)^5199 ≤ (2293411953859/5000000000000 : ℝ)^4175 := by
    have hnat : (2673935813 : ℕ)^5199*5000000000000^4175 ≤ 2293411953859^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673935813 5000000000 2293411953859 5000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409497429/2500000000 : ℝ)^5199 ≤ (5255036046183/50000000000000 : ℝ)^4175 := by
    have hnat : (409497429 : ℕ)^5199*50000000000000^4175 ≤ 5255036046183^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409497429 2500000000 5255036046183 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1284124193/2500000000 : ℝ)^5199 ≤ (4362168881843/10000000000000 : ℝ)^4175 := by
    have hnat : (1284124193 : ℕ)^5199*10000000000000^4175 ≤ 4362168881843^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284124193 2500000000 4362168881843 10000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673935813/5000000000 : ℝ), (-409497429/2500000000 : ℝ), (1284124193/2500000000 : ℝ)] ![(2293411953859/5000000000000 : ℝ), (5255036046183/50000000000000 : ℝ), (4362168881843/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673935813/5000000000 : ℝ)|^5199 ≤ (2293411953859/5000000000000 : ℝ)^4175
        have hw : |(2673935813/5000000000 : ℝ)|=(2673935813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-409497429/2500000000 : ℝ)|^5199 ≤ (5255036046183/50000000000000 : ℝ)^4175
        have hw : |(-409497429/2500000000 : ℝ)|=(409497429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1284124193/2500000000 : ℝ)|^5199 ≤ (4362168881843/10000000000000 : ℝ)^4175
        have hw : |(1284124193/2500000000 : ℝ)|=(1284124193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s4_2 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673935493/5000000000 : ℝ)*x 0 + (2568248921/5000000000 : ℝ)*x 1 + (-409497289/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673935493/5000000000 : ℝ)^5199 ≤ (9173646448323/20000000000000 : ℝ)^4175 := by
    have hnat : (2673935493 : ℕ)^5199*20000000000000^4175 ≤ 9173646448323^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673935493 5000000000 9173646448323 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2568248921/5000000000 : ℝ)^5199 ≤ (545271251677/1250000000000 : ℝ)^4175 := by
    have hnat : (2568248921 : ℕ)^5199*1250000000000^4175 ≤ 545271251677^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568248921 5000000000 545271251677 1250000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (409497289/2500000000 : ℝ)^5199 ≤ (2627516904463/25000000000000 : ℝ)^4175 := by
    have hnat : (409497289 : ℕ)^5199*25000000000000^4175 ≤ 2627516904463^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409497289 2500000000 2627516904463 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673935493/5000000000 : ℝ), (2568248921/5000000000 : ℝ), (-409497289/2500000000 : ℝ)] ![(9173646448323/20000000000000 : ℝ), (545271251677/1250000000000 : ℝ), (2627516904463/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673935493/5000000000 : ℝ)|^5199 ≤ (9173646448323/20000000000000 : ℝ)^4175
        have hw : |(2673935493/5000000000 : ℝ)|=(2673935493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2568248921/5000000000 : ℝ)|^5199 ≤ (545271251677/1250000000000 : ℝ)^4175
        have hw : |(2568248921/5000000000 : ℝ)|=(2568248921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-409497289/2500000000 : ℝ)|^5199 ≤ (2627516904463/25000000000000 : ℝ)^4175
        have hw : |(-409497289/2500000000 : ℝ)|=(409497289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s4_3 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4121756573/10000000000 : ℝ)*x 0 + (3659093793/10000000000 : ℝ)*x 1 + (4621197237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4121756573/10000000000 : ℝ)^5199 ≤ (16582262899931/50000000000000 : ℝ)^4175 := by
    have hnat : (4121756573 : ℕ)^5199*50000000000000^4175 ≤ 16582262899931^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4121756573 10000000000 16582262899931 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3659093793/10000000000 : ℝ)^5199 ≤ (28594493338173/100000000000000 : ℝ)^4175 := by
    have hnat : (3659093793 : ℕ)^5199*100000000000000^4175 ≤ 28594493338173^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3659093793 10000000000 28594493338173 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4621197237/10000000000 : ℝ)^5199 ≤ (38240980856591/100000000000000 : ℝ)^4175 := by
    have hnat : (4621197237 : ℕ)^5199*100000000000000^4175 ≤ 38240980856591^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4621197237 10000000000 38240980856591 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4121756573/10000000000 : ℝ), (3659093793/10000000000 : ℝ), (4621197237/10000000000 : ℝ)] ![(16582262899931/50000000000000 : ℝ), (28594493338173/100000000000000 : ℝ), (38240980856591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4121756573/10000000000 : ℝ)|^5199 ≤ (16582262899931/50000000000000 : ℝ)^4175
        have hw : |(4121756573/10000000000 : ℝ)|=(4121756573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3659093793/10000000000 : ℝ)|^5199 ≤ (28594493338173/100000000000000 : ℝ)^4175
        have hw : |(3659093793/10000000000 : ℝ)|=(3659093793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4621197237/10000000000 : ℝ)|^5199 ≤ (38240980856591/100000000000000 : ℝ)^4175
        have hw : |(4621197237/10000000000 : ℝ)|=(4621197237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s4_4 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1460629653/10000000000 : ℝ)*x 0 + (5140241611/10000000000 : ℝ)*x 1 + (5474668721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1460629653/10000000000 : ℝ)^5199 ≤ (9112285473689/100000000000000 : ℝ)^4175 := by
    have hnat : (1460629653 : ℕ)^5199*100000000000000^4175 ≤ 9112285473689^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460629653 10000000000 9112285473689 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140241611/10000000000 : ℝ)^5199 ≤ (8732259142107/20000000000000 : ℝ)^4175 := by
    have hnat : (5140241611 : ℕ)^5199*20000000000000^4175 ≤ 8732259142107^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140241611 10000000000 8732259142107 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5474668721/10000000000 : ℝ)^5199 ≤ (23613209404151/50000000000000 : ℝ)^4175 := by
    have hnat : (5474668721 : ℕ)^5199*50000000000000^4175 ≤ 23613209404151^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474668721 10000000000 23613209404151 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1460629653/10000000000 : ℝ), (5140241611/10000000000 : ℝ), (5474668721/10000000000 : ℝ)] ![(9112285473689/100000000000000 : ℝ), (8732259142107/20000000000000 : ℝ), (23613209404151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1460629653/10000000000 : ℝ)|^5199 ≤ (9112285473689/100000000000000 : ℝ)^4175
        have hw : |(-1460629653/10000000000 : ℝ)|=(1460629653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140241611/10000000000 : ℝ)|^5199 ≤ (8732259142107/20000000000000 : ℝ)^4175
        have hw : |(5140241611/10000000000 : ℝ)|=(5140241611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5474668721/10000000000 : ℝ)|^5199 ≤ (23613209404151/50000000000000 : ℝ)^4175
        have hw : |(5474668721/10000000000 : ℝ)|=(5474668721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s4_5 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628195163/5000000000 : ℝ)*x 0 + (-649909989/5000000000 : ℝ)*x 1 + (1094933749/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628195163/5000000000 : ℝ)^5199 ≤ (22446612620453/50000000000000 : ℝ)^4175 := by
    have hnat : (2628195163 : ℕ)^5199*50000000000000^4175 ≤ 22446612620453^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628195163 5000000000 22446612620453 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649909989/5000000000 : ℝ)^5199 ≤ (7880355676233/100000000000000 : ℝ)^4175 := by
    have hnat : (649909989 : ℕ)^5199*100000000000000^4175 ≤ 7880355676233^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649909989 5000000000 7880355676233 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094933749/2000000000 : ℝ)^5199 ≤ (23613209533057/50000000000000 : ℝ)^4175 := by
    have hnat : (1094933749 : ℕ)^5199*50000000000000^4175 ≤ 23613209533057^4175*2000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094933749 2000000000 23613209533057 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628195163/5000000000 : ℝ), (-649909989/5000000000 : ℝ), (1094933749/2000000000 : ℝ)] ![(22446612620453/50000000000000 : ℝ), (7880355676233/100000000000000 : ℝ), (23613209533057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628195163/5000000000 : ℝ)|^5199 ≤ (22446612620453/50000000000000 : ℝ)^4175
        have hw : |(2628195163/5000000000 : ℝ)|=(2628195163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-649909989/5000000000 : ℝ)|^5199 ≤ (7880355676233/100000000000000 : ℝ)^4175
        have hw : |(-649909989/5000000000 : ℝ)|=(649909989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1094933749/2000000000 : ℝ)|^5199 ≤ (23613209533057/50000000000000 : ℝ)^4175
        have hw : |(1094933749/2000000000 : ℝ)|=(1094933749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s4_6 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657048793/1250000000 : ℝ)*x 0 + (2737334353/5000000000 : ℝ)*x 1 + (-1299820009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657048793/1250000000 : ℝ)^5199 ≤ (8978645086469/20000000000000 : ℝ)^4175 := by
    have hnat : (657048793 : ℕ)^5199*20000000000000^4175 ≤ 8978645086469^4175*1250000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657048793 1250000000 8978645086469 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737334353/5000000000 : ℝ)^5199 ≤ (4722641864717/10000000000000 : ℝ)^4175 := by
    have hnat : (2737334353 : ℕ)^5199*10000000000000^4175 ≤ 4722641864717^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737334353 5000000000 4722641864717 10000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299820009/10000000000 : ℝ)^5199 ≤ (61565280549/781250000000 : ℝ)^4175 := by
    have hnat : (1299820009 : ℕ)^5199*781250000000^4175 ≤ 61565280549^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299820009 10000000000 61565280549 781250000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657048793/1250000000 : ℝ), (2737334353/5000000000 : ℝ), (-1299820009/10000000000 : ℝ)] ![(8978645086469/20000000000000 : ℝ), (4722641864717/10000000000000 : ℝ), (61565280549/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657048793/1250000000 : ℝ)|^5199 ≤ (8978645086469/20000000000000 : ℝ)^4175
        have hw : |(657048793/1250000000 : ℝ)|=(657048793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737334353/5000000000 : ℝ)|^5199 ≤ (4722641864717/10000000000000 : ℝ)^4175
        have hw : |(2737334353/5000000000 : ℝ)|=(2737334353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1299820009/10000000000 : ℝ)|^5199 ≤ (61565280549/781250000000 : ℝ)^4175
        have hw : |(-1299820009/10000000000 : ℝ)|=(1299820009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s4_7 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2061102493/5000000000 : ℝ)*x 0 + (1152665313/2500000000 : ℝ)*x 1 + (3669781967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2061102493/5000000000 : ℝ)^5199 ≤ (8292254706071/25000000000000 : ℝ)^4175 := by
    have hnat : (2061102493 : ℕ)^5199*25000000000000^4175 ≤ 8292254706071^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061102493 5000000000 8292254706071 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1152665313/2500000000 : ℝ)^5199 ≤ (9533110109959/25000000000000 : ℝ)^4175 := by
    have hnat : (1152665313 : ℕ)^5199*25000000000000^4175 ≤ 9533110109959^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152665313 2500000000 9533110109959 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3669781967/10000000000 : ℝ)^5199 ≤ (14349270358703/50000000000000 : ℝ)^4175 := by
    have hnat : (3669781967 : ℕ)^5199*50000000000000^4175 ≤ 14349270358703^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3669781967 10000000000 14349270358703 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2061102493/5000000000 : ℝ), (1152665313/2500000000 : ℝ), (3669781967/10000000000 : ℝ)] ![(8292254706071/25000000000000 : ℝ), (9533110109959/25000000000000 : ℝ), (14349270358703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2061102493/5000000000 : ℝ)|^5199 ≤ (8292254706071/25000000000000 : ℝ)^4175
        have hw : |(2061102493/5000000000 : ℝ)|=(2061102493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1152665313/2500000000 : ℝ)|^5199 ≤ (9533110109959/25000000000000 : ℝ)^4175
        have hw : |(1152665313/2500000000 : ℝ)|=(1152665313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3669781967/10000000000 : ℝ)|^5199 ≤ (14349270358703/50000000000000 : ℝ)^4175
        have hw : |(3669781967/10000000000 : ℝ)|=(3669781967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1697_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8593/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4949/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9899/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3437/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8593/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4949/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8593/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4949/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8593/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4949/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8593/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4949/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8593/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4949/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8593/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4949/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4949/50000 : ℝ) ^ (5191/1024 : ℝ) ≤ (809268410342637/100000000000000000000 : ℝ) := by
    have hpowers : (4949/50000 : ℝ)^5191 ≤ (809268410342637/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4949 : ℕ)^5191*100000000000000000000^1024 ≤ 809268410342637^1024*50000^5191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4949 50000 809268410342637 100000000000000000000 5191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4949/50000 : ℝ)) (X := (809268410342637/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8593/50000 : ℝ) ^ (5191/1024 : ℝ) ≤ (103665487865661/781250000000000000 : ℝ) := by
    have hpowers : (8593/50000 : ℝ)^5191 ≤ (103665487865661/781250000000000000 : ℝ)^1024 := by
      have hnat : (8593 : ℕ)^5191*781250000000000000^1024 ≤ 103665487865661^1024*50000^5191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8593 50000 103665487865661 781250000000000000 5191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8593/50000 : ℝ)) (X := (103665487865661/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000809268410342637/50000000000000000000 : ℝ) ≤ (625001995486103/625000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (50000809268410342637/50000000000000000000 : ℝ)^1024 ≤ (625001995486103/625000000000000 : ℝ)^5191 := by
      have hnat : (50000809268410342637 : ℕ)^1024*625000000000000^5191 ≤ 625001995486103^5191*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000809268410342637 50000000000000000000 625001995486103 625000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625001995486103/625000000000000 : ℝ)) (X := (50000809268410342637/50000000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20002815690171429449/20000000000000000000 : ℝ) ≤ (80002221617281/80000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (20002815690171429449/20000000000000000000 : ℝ)^1024 ≤ (80002221617281/80000000000000 : ℝ)^5191 := by
      have hnat : (20002815690171429449 : ℕ)^1024*80000000000000^5191 ≤ 80002221617281^5191*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20002815690171429449 20000000000000000000 80002221617281 80000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80002221617281/80000000000000 : ℝ)) (X := (20002815690171429449/20000000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (390728665487865661/390625000000000000 : ℝ) ≤ (5000261738271301/5000000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (390728665487865661/390625000000000000 : ℝ)^1024 ≤ (5000261738271301/5000000000000000 : ℝ)^5191 := by
      have hnat : (390728665487865661 : ℕ)^1024*5000000000000000^5191 ≤ 5000261738271301^5191*390625000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390728665487865661 390625000000000000 5000261738271301 5000000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000261738271301/5000000000000000 : ℝ)) (X := (390728665487865661/390625000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(809268410342637/100000000000000000000 : ℝ) ≤ ((18218841834991995983/18220000000000000000 : ℝ)+2*(245774382477/728800000000000 : ℝ)*(4949/50000 : ℝ))^(5191/1024 : ℝ) := by
    rw [show (18218841834991995983/18220000000000000000 : ℝ)+2*(245774382477/728800000000000 : ℝ)*(4949/50000 : ℝ)=(625001995486103/625000000000000 : ℝ) by norm_num, show 1+2*(809268410342637/100000000000000000000 : ℝ)=(50000809268410342637/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(103665487865661/781250000000000000 : ℝ)+(809268410342637/100000000000000000000 : ℝ) ≤ ((18218841834991995983/18220000000000000000 : ℝ)+(245774382477/728800000000000 : ℝ)*((8593/50000 : ℝ)+(4949/50000 : ℝ)))^(5191/1024 : ℝ) := by
    rw [show (18218841834991995983/18220000000000000000 : ℝ)+(245774382477/728800000000000 : ℝ)*((8593/50000 : ℝ)+(4949/50000 : ℝ))=(80002221617281/80000000000000 : ℝ) by norm_num, show 1+(103665487865661/781250000000000000 : ℝ)+(809268410342637/100000000000000000000 : ℝ)=(20002815690171429449/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(103665487865661/781250000000000000 : ℝ) ≤ ((18218841834991995983/18220000000000000000 : ℝ)+2*(245774382477/728800000000000 : ℝ)*(8593/50000 : ℝ))^(5191/1024 : ℝ) := by
    rw [show (18218841834991995983/18220000000000000000 : ℝ)+2*(245774382477/728800000000000 : ℝ)*(8593/50000 : ℝ)=(5000261738271301/5000000000000000 : ℝ) by norm_num, show 1+2*(103665487865661/781250000000000000 : ℝ)=(390728665487865661/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18218841834991995983/18220000000000000000 : ℝ)*(X 1 0+X 2 0)+(245774382477/728800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (4949/50000 : ℝ)) (hi := (8593/50000 : ℝ)) (c := (18218841834991995983/18220000000000000000 : ℝ)) (alpha := (245774382477/728800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18218841834991995983/18220000000000000000 : ℝ)*(X 0 1+X 2 1)+(245774382477/728800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (4949/50000 : ℝ)) (hi := (8593/50000 : ℝ)) (c := (18218841834991995983/18220000000000000000 : ℝ)) (alpha := (245774382477/728800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18218841834991995983/18220000000000000000 : ℝ)*(X 0 2+X 1 2)+(245774382477/728800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (4949/50000 : ℝ)) (hi := (8593/50000 : ℝ)) (c := (18218841834991995983/18220000000000000000 : ℝ)) (alpha := (245774382477/728800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-365118001/2500000000 : ℝ)*X 0 0+(684808699/1250000000 : ℝ)*X 0 1+(2568248323/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673935813/5000000000 : ℝ)*X 1 0+(-409497429/2500000000 : ℝ)*X 1 1+(1284124193/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673935493/5000000000 : ℝ)*X 2 0+(2568248921/5000000000 : ℝ)*X 2 1+(-409497289/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4121756573/10000000000 : ℝ)*X 0 0+(3659093793/10000000000 : ℝ)*X 0 1+(4621197237/10000000000 : ℝ)*X 0 2+(4121756573/10000000000 : ℝ)*X 1 0+(3659093793/10000000000 : ℝ)*X 1 1+(4621197237/10000000000 : ℝ)*X 1 2+(4121756573/10000000000 : ℝ)*X 2 0+(3659093793/10000000000 : ℝ)*X 2 1+(4621197237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1460629653/10000000000 : ℝ)*X 0 0+(5140241611/10000000000 : ℝ)*X 0 1+(5474668721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628195163/5000000000 : ℝ)*X 1 0+(-649909989/5000000000 : ℝ)*X 1 1+(1094933749/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((657048793/1250000000 : ℝ)*X 2 0+(2737334353/5000000000 : ℝ)*X 2 1+(-1299820009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2061102493/5000000000 : ℝ)*X 0 0+(1152665313/2500000000 : ℝ)*X 0 1+(3669781967/10000000000 : ℝ)*X 0 2+(2061102493/5000000000 : ℝ)*X 1 0+(1152665313/2500000000 : ℝ)*X 1 1+(3669781967/10000000000 : ℝ)*X 1 2+(2061102493/5000000000 : ℝ)*X 2 0+(1152665313/2500000000 : ℝ)*X 2 1+(3669781967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (164608745962037133670316313/113875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (977406983/50000000000000 : ℝ)*(base19) + (705980931/100000000000000 : ℝ)*(base23) + (2890173/4000000000000 : ℝ)*(lower3) + (30044167/6250000000000 : ℝ)*(upper4) + (35266747/10000000000000 : ℝ)*(lower5) + (495459358960337/25000000000000 : ℝ)*(major0) + (495459358960337/25000000000000 : ℝ)*(major1) + (495459358960337/25000000000000 : ℝ)*(major2) + (584847633107421/20000000000000 : ℝ)*(sp0) + (365533443815407/12500000000000 : ℝ)*(sp1) + (731067199839073/25000000000000 : ℝ)*(sp2) + (259848986841567/25000000000000 : ℝ)*(sp3) + (15669900059/50000000000000 : ℝ)*(sp4) + (4685397577/50000000000000 : ℝ)*(sp7) + (519702659080711/50000000000000 : ℝ)*(f.failure) + (1462134752668611/50000000000000 : ℝ)*(f.sum) + (13425655316009/9110000000000000000000000000 : ℝ)*base65 + (2971744505015948729/455500000000000000000000000000000 : ℝ)*base68 + (3513005932051948729/455500000000000000000000000000000 : ℝ)*base70 + (156910504777051271/455500000000000000000000000000000 : ℝ)*base71 + (44105835833211/9110000000000000000000000000 : ℝ)*base74 + (3662032196833948729/455500000000000000000000000000000 : ℝ)*base76 + (3144466793530948729/455500000000000000000000000000000 : ℝ)*base78 + (1054363081048948729/455500000000000000000000000000000 : ℝ)*base80 + (24531565689729/9110000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (13116809/5000000000000000000000 : ℝ)*base89 + (13116809/5000000000000000000000 : ℝ)*base91 + (13116809/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4001611313897410191564940611/455500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (316368589/25000000000000 : ℝ)*(base19) + (28185311/2000000000000 : ℝ)*(base23) + (19495953/5000000000000 : ℝ)*(lower1) + (94963213/50000000000000 : ℝ)*(upper3) + (31508727/50000000000000 : ℝ)*(lower4) + (194140459/100000000000000 : ℝ)*(upper5) + (1013251847939813/50000000000000 : ℝ)*(major0) + (1013251847939813/50000000000000 : ℝ)*(major1) + (1013251847939813/50000000000000 : ℝ)*(major2) + (392569181/50000000000000 : ℝ)*(sp2) + (1495087934669303/50000000000000 : ℝ)*(sp4) + (11960698415457/400000000000 : ℝ)*(sp5) + (1495086837467347/50000000000000 : ℝ)*(sp6) + (10628312295841/1000000000000 : ℝ)*(sp7) + (10628312295841/1000000000000 : ℝ)*(f.failure) + (1495087934669303/50000000000000 : ℝ)*(f.sum) + (57366929426761/18220000000000000000000000000 : ℝ)*base65 + (6901033511784203821/911000000000000000000000000000000 : ℝ)*base68 + (4729246097544203821/911000000000000000000000000000000 : ℝ)*base70 + (4532379429358203821/911000000000000000000000000000000 : ℝ)*base72 + (30214249782801/18220000000000000000000000000 : ℝ)*base73 + (19735168245708203821/911000000000000000000000000000000 : ℝ)*base76 + (5070155636406203821/911000000000000000000000000000000 : ℝ)*base78 + (3539412995106203821/911000000000000000000000000000000 : ℝ)*base80 + (42065935584761/18220000000000000000000000000 : ℝ)*base81 + (156721/100000000000000000000 : ℝ)*base90 + (156721/100000000000000000000 : ℝ)*base92 + (156721/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1697_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8593/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4949/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9899/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3437/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1697_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1697_box_0 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1131433527/10000000000 : ℝ)*x 0 + (542421047/1000000000 : ℝ)*x 1 + (216968413/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1131433527/10000000000 : ℝ)^5199 ≤ (662999421297/10000000000000 : ℝ)^4175 := by
    have hnat : (1131433527 : ℕ)^5199*10000000000000^4175 ≤ 662999421297^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131433527 10000000000 662999421297 10000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542421047/1000000000 : ℝ)^5199 ≤ (11671250915293/25000000000000 : ℝ)^4175 := by
    have hnat : (542421047 : ℕ)^5199*25000000000000^4175 ≤ 11671250915293^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542421047 1000000000 11671250915293 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216968413/400000000 : ℝ)^5199 ≤ (46685002107097/100000000000000 : ℝ)^4175 := by
    have hnat : (216968413 : ℕ)^5199*100000000000000^4175 ≤ 46685002107097^4175*400000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216968413 400000000 46685002107097 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1131433527/10000000000 : ℝ), (542421047/1000000000 : ℝ), (216968413/400000000 : ℝ)] ![(662999421297/10000000000000 : ℝ), (11671250915293/25000000000000 : ℝ), (46685002107097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1131433527/10000000000 : ℝ)|^5199 ≤ (662999421297/10000000000000 : ℝ)^4175
        have hw : |(-1131433527/10000000000 : ℝ)|=(1131433527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542421047/1000000000 : ℝ)|^5199 ≤ (11671250915293/25000000000000 : ℝ)^4175
        have hw : |(542421047/1000000000 : ℝ)|=(542421047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216968413/400000000 : ℝ)|^5199 ≤ (46685002107097/100000000000000 : ℝ)^4175
        have hw : |(216968413/400000000 : ℝ)|=(216968413/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_1 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612948187/5000000000 : ℝ)*x 0 + (-176659129/1250000000 : ℝ)*x 1 + (5424210309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612948187/5000000000 : ℝ)^5199 ≤ (44569138911397/100000000000000 : ℝ)^4175 := by
    have hnat : (2612948187 : ℕ)^5199*100000000000000^4175 ≤ 44569138911397^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612948187 5000000000 44569138911397 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176659129/1250000000 : ℝ)^5199 ≤ (68327024547/781250000000 : ℝ)^4175 := by
    have hnat : (176659129 : ℕ)^5199*781250000000^4175 ≤ 68327024547^4175*1250000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176659129 1250000000 68327024547 781250000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424210309/10000000000 : ℝ)^5199 ≤ (11671250483903/25000000000000 : ℝ)^4175 := by
    have hnat : (5424210309 : ℕ)^5199*25000000000000^4175 ≤ 11671250483903^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424210309 10000000000 11671250483903 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612948187/5000000000 : ℝ), (-176659129/1250000000 : ℝ), (5424210309/10000000000 : ℝ)] ![(44569138911397/100000000000000 : ℝ), (68327024547/781250000000 : ℝ), (11671250483903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612948187/5000000000 : ℝ)|^5199 ≤ (44569138911397/100000000000000 : ℝ)^4175
        have hw : |(2612948187/5000000000 : ℝ)|=(2612948187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-176659129/1250000000 : ℝ)|^5199 ≤ (68327024547/781250000000 : ℝ)^4175
        have hw : |(-176659129/1250000000 : ℝ)|=(176659129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424210309/10000000000 : ℝ)|^5199 ≤ (11671250483903/25000000000000 : ℝ)^4175
        have hw : |(5424210309/10000000000 : ℝ)|=(5424210309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_2 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225896363/10000000000 : ℝ)*x 0 + (542421033/1000000000 : ℝ)*x 1 + (-706636509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225896363/10000000000 : ℝ)^5199 ≤ (44569138794573/100000000000000 : ℝ)^4175 := by
    have hnat : (5225896363 : ℕ)^5199*100000000000000^4175 ≤ 44569138794573^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225896363 10000000000 44569138794573 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542421033/1000000000 : ℝ)^5199 ≤ (9337000432137/20000000000000 : ℝ)^4175 := by
    have hnat : (542421033 : ℕ)^5199*20000000000000^4175 ≤ 9337000432137^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542421033 1000000000 9337000432137 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (706636509/5000000000 : ℝ)^5199 ≤ (8745859034129/100000000000000 : ℝ)^4175 := by
    have hnat : (706636509 : ℕ)^5199*100000000000000^4175 ≤ 8745859034129^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706636509 5000000000 8745859034129 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225896363/10000000000 : ℝ), (542421033/1000000000 : ℝ), (-706636509/5000000000 : ℝ)] ![(44569138794573/100000000000000 : ℝ), (9337000432137/20000000000000 : ℝ), (8745859034129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225896363/10000000000 : ℝ)|^5199 ≤ (44569138794573/100000000000000 : ℝ)^4175
        have hw : |(5225896363/10000000000 : ℝ)|=(5225896363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542421033/1000000000 : ℝ)|^5199 ≤ (9337000432137/20000000000000 : ℝ)^4175
        have hw : |(542421033/1000000000 : ℝ)|=(542421033/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-706636509/5000000000 : ℝ)|^5199 ≤ (8745859034129/100000000000000 : ℝ)^4175
        have hw : |(-706636509/5000000000 : ℝ)|=(706636509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_3 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4505135851/10000000000 : ℝ)*x 0 + (123510561/312500000 : ℝ)*x 1 + (1976168947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4505135851/10000000000 : ℝ)^5199 ≤ (9262175833147/25000000000000 : ℝ)^4175 := by
    have hnat : (4505135851 : ℕ)^5199*25000000000000^4175 ≤ 9262175833147^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505135851 10000000000 9262175833147 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123510561/312500000 : ℝ)^5199 ≤ (629512972297/2000000000000 : ℝ)^4175 := by
    have hnat : (123510561 : ℕ)^5199*2000000000000^4175 ≤ 629512972297^4175*312500000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123510561 312500000 629512972297 2000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1976168947/5000000000 : ℝ)^5199 ≤ (31475648039659/100000000000000 : ℝ)^4175 := by
    have hnat : (1976168947 : ℕ)^5199*100000000000000^4175 ≤ 31475648039659^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976168947 5000000000 31475648039659 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4505135851/10000000000 : ℝ), (123510561/312500000 : ℝ), (1976168947/5000000000 : ℝ)] ![(9262175833147/25000000000000 : ℝ), (629512972297/2000000000000 : ℝ), (31475648039659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4505135851/10000000000 : ℝ)|^5199 ≤ (9262175833147/25000000000000 : ℝ)^4175
        have hw : |(4505135851/10000000000 : ℝ)|=(4505135851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(123510561/312500000 : ℝ)|^5199 ≤ (629512972297/2000000000000 : ℝ)^4175
        have hw : |(123510561/312500000 : ℝ)|=(123510561/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1976168947/5000000000 : ℝ)|^5199 ≤ (31475648039659/100000000000000 : ℝ)^4175
        have hw : |(1976168947/5000000000 : ℝ)|=(1976168947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_4 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1810351993/10000000000 : ℝ)*x 0 + (2588370531/5000000000 : ℝ)*x 1 + (5176740971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1810351993/10000000000 : ℝ)^5199 ≤ (297615105521/2500000000000 : ℝ)^4175 := by
    have hnat : (1810351993 : ℕ)^5199*2500000000000^4175 ≤ 297615105521^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810351993 10000000000 297615105521 2500000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588370531/5000000000 : ℝ)^5199 ≤ (1376490573899/3125000000000 : ℝ)^4175 := by
    have hnat : (2588370531 : ℕ)^5199*3125000000000^4175 ≤ 1376490573899^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588370531 5000000000 1376490573899 3125000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176740971/10000000000 : ℝ)^5199 ≤ (22023848700279/50000000000000 : ℝ)^4175 := by
    have hnat : (5176740971 : ℕ)^5199*50000000000000^4175 ≤ 22023848700279^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176740971 10000000000 22023848700279 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1810351993/10000000000 : ℝ), (2588370531/5000000000 : ℝ), (5176740971/10000000000 : ℝ)] ![(297615105521/2500000000000 : ℝ), (1376490573899/3125000000000 : ℝ), (22023848700279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1810351993/10000000000 : ℝ)|^5199 ≤ (297615105521/2500000000000 : ℝ)^4175
        have hw : |(-1810351993/10000000000 : ℝ)|=(1810351993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588370531/5000000000 : ℝ)|^5199 ≤ (1376490573899/3125000000000 : ℝ)^4175
        have hw : |(2588370531/5000000000 : ℝ)|=(2588370531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176740971/10000000000 : ℝ)|^5199 ≤ (22023848700279/50000000000000 : ℝ)^4175
        have hw : |(5176740971/10000000000 : ℝ)|=(5176740971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_5 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394255431/10000000000 : ℝ)*x 0 + (-304314487/2000000000 : ℝ)*x 1 + (5176741031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394255431/10000000000 : ℝ)^5199 ≤ (2318208517351/5000000000000 : ℝ)^4175 := by
    have hnat : (5394255431 : ℕ)^5199*5000000000000^4175 ≤ 2318208517351^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394255431 10000000000 2318208517351 5000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (304314487/2000000000 : ℝ)^5199 ≤ (4794065802421/50000000000000 : ℝ)^4175 := by
    have hnat : (304314487 : ℕ)^5199*50000000000000^4175 ≤ 4794065802421^4175*2000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304314487 2000000000 4794065802421 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176741031/10000000000 : ℝ)^5199 ≤ (44047698036301/100000000000000 : ℝ)^4175 := by
    have hnat : (5176741031 : ℕ)^5199*100000000000000^4175 ≤ 44047698036301^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176741031 10000000000 44047698036301 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394255431/10000000000 : ℝ), (-304314487/2000000000 : ℝ), (5176741031/10000000000 : ℝ)] ![(2318208517351/5000000000000 : ℝ), (4794065802421/50000000000000 : ℝ), (44047698036301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394255431/10000000000 : ℝ)|^5199 ≤ (2318208517351/5000000000000 : ℝ)^4175
        have hw : |(5394255431/10000000000 : ℝ)|=(5394255431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-304314487/2000000000 : ℝ)|^5199 ≤ (4794065802421/50000000000000 : ℝ)^4175
        have hw : |(-304314487/2000000000 : ℝ)|=(304314487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176741031/10000000000 : ℝ)|^5199 ≤ (44047698036301/100000000000000 : ℝ)^4175
        have hw : |(5176741031/10000000000 : ℝ)|=(5176741031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_6 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394255491/10000000000 : ℝ)*x 0 + (2588370479/5000000000 : ℝ)*x 1 + (-380393113/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394255491/10000000000 : ℝ)^5199 ≤ (46364170989213/100000000000000 : ℝ)^4175 := by
    have hnat : (5394255491 : ℕ)^5199*100000000000000^4175 ≤ 46364170989213^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394255491 10000000000 46364170989213 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588370479/5000000000 : ℝ)^5199 ≤ (22023848631407/50000000000000 : ℝ)^4175 := by
    have hnat : (2588370479 : ℕ)^5199*50000000000000^4175 ≤ 22023848631407^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588370479 5000000000 22023848631407 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (380393113/2500000000 : ℝ)^5199 ≤ (4794065869121/50000000000000 : ℝ)^4175 := by
    have hnat : (380393113 : ℕ)^5199*50000000000000^4175 ≤ 4794065869121^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380393113 2500000000 4794065869121 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394255491/10000000000 : ℝ), (2588370479/5000000000 : ℝ), (-380393113/2500000000 : ℝ)] ![(46364170989213/100000000000000 : ℝ), (22023848631407/50000000000000 : ℝ), (4794065869121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394255491/10000000000 : ℝ)|^5199 ≤ (46364170989213/100000000000000 : ℝ)^4175
        have hw : |(5394255491/10000000000 : ℝ)|=(5394255491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588370479/5000000000 : ℝ)|^5199 ≤ (22023848631407/50000000000000 : ℝ)^4175
        have hw : |(2588370479/5000000000 : ℝ)|=(2588370479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-380393113/2500000000 : ℝ)|^5199 ≤ (4794065869121/50000000000000 : ℝ)^4175
        have hw : |(-380393113/2500000000 : ℝ)|=(380393113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_7 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (744685499/2000000000 : ℝ)*x 0 + (542792927/1250000000 : ℝ)*x 1 + (868468679/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (744685499/2000000000 : ℝ)^5199 ≤ (29221889760827/100000000000000 : ℝ)^4175 := by
    have hnat : (744685499 : ℕ)^5199*100000000000000^4175 ≤ 29221889760827^4175*2000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744685499 2000000000 29221889760827 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542792927/1250000000 : ℝ)^5199 ≤ (17694527610741/50000000000000 : ℝ)^4175 := by
    have hnat : (542792927 : ℕ)^5199*50000000000000^4175 ≤ 17694527610741^4175*1250000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542792927 1250000000 17694527610741 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (868468679/2000000000 : ℝ)^5199 ≤ (35389055008361/100000000000000 : ℝ)^4175 := by
    have hnat : (868468679 : ℕ)^5199*100000000000000^4175 ≤ 35389055008361^4175*2000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868468679 2000000000 35389055008361 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(744685499/2000000000 : ℝ), (542792927/1250000000 : ℝ), (868468679/2000000000 : ℝ)] ![(29221889760827/100000000000000 : ℝ), (17694527610741/50000000000000 : ℝ), (35389055008361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(744685499/2000000000 : ℝ)|^5199 ≤ (29221889760827/100000000000000 : ℝ)^4175
        have hw : |(744685499/2000000000 : ℝ)|=(744685499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542792927/1250000000 : ℝ)|^5199 ≤ (17694527610741/50000000000000 : ℝ)^4175
        have hw : |(542792927/1250000000 : ℝ)|=(542792927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(868468679/2000000000 : ℝ)|^5199 ≤ (35389055008361/100000000000000 : ℝ)^4175
        have hw : |(868468679/2000000000 : ℝ)|=(868468679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_8 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-832272041/5000000000 : ℝ)*x 0 + (1248692841/2500000000 : ℝ)*x 1 + (273374641/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (832272041/5000000000 : ℝ)^5199 ≤ (2680666751877/25000000000000 : ℝ)^4175 := by
    have hnat : (832272041 : ℕ)^5199*25000000000000^4175 ≤ 2680666751877^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832272041 5000000000 2680666751877 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1248692841/2500000000 : ℝ)^5199 ≤ (1053199656393/2500000000000 : ℝ)^4175 := by
    have hnat : (1248692841 : ℕ)^5199*2500000000000^4175 ≤ 1053199656393^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248692841 2500000000 1053199656393 2500000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273374641/500000000 : ℝ)^5199 ≤ (9429869344687/20000000000000 : ℝ)^4175 := by
    have hnat : (273374641 : ℕ)^5199*20000000000000^4175 ≤ 9429869344687^4175*500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273374641 500000000 9429869344687 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-832272041/5000000000 : ℝ), (1248692841/2500000000 : ℝ), (273374641/500000000 : ℝ)] ![(2680666751877/25000000000000 : ℝ), (1053199656393/2500000000000 : ℝ), (9429869344687/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-832272041/5000000000 : ℝ)|^5199 ≤ (2680666751877/25000000000000 : ℝ)^4175
        have hw : |(-832272041/5000000000 : ℝ)|=(832272041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1248692841/2500000000 : ℝ)|^5199 ≤ (1053199656393/2500000000000 : ℝ)^4175
        have hw : |(1248692841/2500000000 : ℝ)|=(1248692841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(273374641/500000000 : ℝ)|^5199 ≤ (9429869344687/20000000000000 : ℝ)^4175
        have hw : |(273374641/500000000 : ℝ)|=(273374641/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_9 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196464847/10000000000 : ℝ)*x 0 + (-1393516053/10000000000 : ℝ)*x 1 + (2733746399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196464847/10000000000 : ℝ)^5199 ≤ (44256783451277/100000000000000 : ℝ)^4175 := by
    have hnat : (5196464847 : ℕ)^5199*100000000000000^4175 ≤ 44256783451277^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196464847 10000000000 44256783451277 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1393516053/10000000000 : ℝ)^5199 ≤ (8593870037231/100000000000000 : ℝ)^4175 := by
    have hnat : (1393516053 : ℕ)^5199*100000000000000^4175 ≤ 8593870037231^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393516053 10000000000 8593870037231 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733746399/5000000000 : ℝ)^5199 ≤ (2946834155449/6250000000000 : ℝ)^4175 := by
    have hnat : (2733746399 : ℕ)^5199*6250000000000^4175 ≤ 2946834155449^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733746399 5000000000 2946834155449 6250000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196464847/10000000000 : ℝ), (-1393516053/10000000000 : ℝ), (2733746399/5000000000 : ℝ)] ![(44256783451277/100000000000000 : ℝ), (8593870037231/100000000000000 : ℝ), (2946834155449/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196464847/10000000000 : ℝ)|^5199 ≤ (44256783451277/100000000000000 : ℝ)^4175
        have hw : |(5196464847/10000000000 : ℝ)|=(5196464847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1393516053/10000000000 : ℝ)|^5199 ≤ (8593870037231/100000000000000 : ℝ)^4175
        have hw : |(-1393516053/10000000000 : ℝ)|=(1393516053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733746399/5000000000 : ℝ)|^5199 ≤ (2946834155449/6250000000000 : ℝ)^4175
        have hw : |(2733746399/5000000000 : ℝ)|=(2733746399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_10 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299116597/2500000000 : ℝ)*x 0 + (2733745833/5000000000 : ℝ)*x 1 + (-139351551/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299116597/2500000000 : ℝ)^5199 ≤ (8851359958901/20000000000000 : ℝ)^4175 := by
    have hnat : (1299116597 : ℕ)^5199*20000000000000^4175 ≤ 8851359958901^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299116597 2500000000 8851359958901 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733745833/5000000000 : ℝ)^5199 ≤ (47149334331001/100000000000000 : ℝ)^4175 := by
    have hnat : (2733745833 : ℕ)^5199*100000000000000^4175 ≤ 47149334331001^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733745833 5000000000 47149334331001 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139351551/1000000000 : ℝ)^5199 ≤ (4296932933597/50000000000000 : ℝ)^4175 := by
    have hnat : (139351551 : ℕ)^5199*50000000000000^4175 ≤ 4296932933597^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139351551 1000000000 4296932933597 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299116597/2500000000 : ℝ), (2733745833/5000000000 : ℝ), (-139351551/1000000000 : ℝ)] ![(8851359958901/20000000000000 : ℝ), (47149334331001/100000000000000 : ℝ), (4296932933597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299116597/2500000000 : ℝ)|^5199 ≤ (8851359958901/20000000000000 : ℝ)^4175
        have hw : |(1299116597/2500000000 : ℝ)|=(1299116597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733745833/5000000000 : ℝ)|^5199 ≤ (47149334331001/100000000000000 : ℝ)^4175
        have hw : |(2733745833/5000000000 : ℝ)|=(2733745833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-139351551/1000000000 : ℝ)|^5199 ≤ (4296932933597/50000000000000 : ℝ)^4175
        have hw : |(-139351551/1000000000 : ℝ)|=(139351551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_11 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (463684553/1000000000 : ℝ)*x 0 + (1941971601/5000000000 : ℝ)*x 1 + (388394973/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (463684553/1000000000 : ℝ)^5199 ≤ (9600574914057/25000000000000 : ℝ)^4175 := by
    have hnat : (463684553 : ℕ)^5199*25000000000000^4175 ≤ 9600574914057^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463684553 1000000000 9600574914057 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1941971601/5000000000 : ℝ)^5199 ≤ (3079881793323/10000000000000 : ℝ)^4175 := by
    have hnat : (1941971601 : ℕ)^5199*10000000000000^4175 ≤ 3079881793323^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941971601 5000000000 3079881793323 10000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (388394973/1000000000 : ℝ)^5199 ≤ (246391059163/800000000000 : ℝ)^4175 := by
    have hnat : (388394973 : ℕ)^5199*800000000000^4175 ≤ 246391059163^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388394973 1000000000 246391059163 800000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(463684553/1000000000 : ℝ), (1941971601/5000000000 : ℝ), (388394973/1000000000 : ℝ)] ![(9600574914057/25000000000000 : ℝ), (3079881793323/10000000000000 : ℝ), (246391059163/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(463684553/1000000000 : ℝ)|^5199 ≤ (9600574914057/25000000000000 : ℝ)^4175
        have hw : |(463684553/1000000000 : ℝ)|=(463684553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1941971601/5000000000 : ℝ)|^5199 ≤ (3079881793323/10000000000000 : ℝ)^4175
        have hw : |(1941971601/5000000000 : ℝ)|=(1941971601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(388394973/1000000000 : ℝ)|^5199 ≤ (246391059163/800000000000 : ℝ)^4175
        have hw : |(388394973/1000000000 : ℝ)|=(388394973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_12 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1272189541/10000000000 : ℝ)*x 0 + (1399325597/2500000000 : ℝ)*x 1 + (5151492563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1272189541/10000000000 : ℝ)^5199 ≤ (7672302690999/100000000000000 : ℝ)^4175 := by
    have hnat : (1272189541 : ℕ)^5199*100000000000000^4175 ≤ 7672302690999^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272189541 10000000000 7672302690999 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1399325597/2500000000 : ℝ)^5199 ≤ (48547364527867/100000000000000 : ℝ)^4175 := by
    have hnat : (1399325597 : ℕ)^5199*100000000000000^4175 ≤ 48547364527867^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1399325597 2500000000 48547364527867 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151492563/10000000000 : ℝ)^5199 ≤ (1751213310811/4000000000000 : ℝ)^4175 := by
    have hnat : (5151492563 : ℕ)^5199*4000000000000^4175 ≤ 1751213310811^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151492563 10000000000 1751213310811 4000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1272189541/10000000000 : ℝ), (1399325597/2500000000 : ℝ), (5151492563/10000000000 : ℝ)] ![(7672302690999/100000000000000 : ℝ), (48547364527867/100000000000000 : ℝ), (1751213310811/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1272189541/10000000000 : ℝ)|^5199 ≤ (7672302690999/100000000000000 : ℝ)^4175
        have hw : |(-1272189541/10000000000 : ℝ)|=(1272189541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1399325597/2500000000 : ℝ)|^5199 ≤ (48547364527867/100000000000000 : ℝ)^4175
        have hw : |(1399325597/2500000000 : ℝ)|=(1399325597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5151492563/10000000000 : ℝ)|^5199 ≤ (1751213310811/4000000000000 : ℝ)^4175
        have hw : |(5151492563/10000000000 : ℝ)|=(5151492563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_13 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (676432589/1250000000 : ℝ)*x 0 + (-1532157953/10000000000 : ℝ)*x 1 + (1287873281/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676432589/1250000000 : ℝ)^5199 ≤ (23274197086617/50000000000000 : ℝ)^4175 := by
    have hnat : (676432589 : ℕ)^5199*50000000000000^4175 ≤ 23274197086617^4175*1250000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676432589 1250000000 23274197086617 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1532157953/10000000000 : ℝ)^5199 ≤ (9671267107687/100000000000000 : ℝ)^4175 := by
    have hnat : (1532157953 : ℕ)^5199*100000000000000^4175 ≤ 9671267107687^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1532157953 10000000000 9671267107687 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1287873281/2500000000 : ℝ)^5199 ≤ (8756067741469/20000000000000 : ℝ)^4175 := by
    have hnat : (1287873281 : ℕ)^5199*20000000000000^4175 ≤ 8756067741469^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287873281 2500000000 8756067741469 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676432589/1250000000 : ℝ), (-1532157953/10000000000 : ℝ), (1287873281/2500000000 : ℝ)] ![(23274197086617/50000000000000 : ℝ), (9671267107687/100000000000000 : ℝ), (8756067741469/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676432589/1250000000 : ℝ)|^5199 ≤ (23274197086617/50000000000000 : ℝ)^4175
        have hw : |(676432589/1250000000 : ℝ)|=(676432589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1532157953/10000000000 : ℝ)|^5199 ≤ (9671267107687/100000000000000 : ℝ)^4175
        have hw : |(-1532157953/10000000000 : ℝ)|=(1532157953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1287873281/2500000000 : ℝ)|^5199 ≤ (8756067741469/20000000000000 : ℝ)^4175
        have hw : |(1287873281/2500000000 : ℝ)|=(1287873281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_14 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082292337/2000000000 : ℝ)*x 0 + (1287872959/2500000000 : ℝ)*x 1 + (-1532158361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082292337/2000000000 : ℝ)^5199 ≤ (46548404595601/100000000000000 : ℝ)^4175 := by
    have hnat : (1082292337 : ℕ)^5199*100000000000000^4175 ≤ 46548404595601^4175*2000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082292337 2000000000 46548404595601 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1287872959/2500000000 : ℝ)^5199 ≤ (5472540634553/12500000000000 : ℝ)^4175 := by
    have hnat : (1287872959 : ℕ)^5199*12500000000000^4175 ≤ 5472540634553^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287872959 2500000000 5472540634553 12500000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1532158361/10000000000 : ℝ)^5199 ≤ (60445439467/625000000000 : ℝ)^4175 := by
    have hnat : (1532158361 : ℕ)^5199*625000000000^4175 ≤ 60445439467^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1532158361 10000000000 60445439467 625000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082292337/2000000000 : ℝ), (1287872959/2500000000 : ℝ), (-1532158361/10000000000 : ℝ)] ![(46548404595601/100000000000000 : ℝ), (5472540634553/12500000000000 : ℝ), (60445439467/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082292337/2000000000 : ℝ)|^5199 ≤ (46548404595601/100000000000000 : ℝ)^4175
        have hw : |(1082292337/2000000000 : ℝ)|=(1082292337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1287872959/2500000000 : ℝ)|^5199 ≤ (5472540634553/12500000000000 : ℝ)^4175
        have hw : |(1287872959/2500000000 : ℝ)|=(1287872959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1532158361/10000000000 : ℝ)|^5199 ≤ (60445439467/625000000000 : ℝ)^4175
        have hw : |(-1532158361/10000000000 : ℝ)|=(1532158361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_box_15 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (728138001/2000000000 : ℝ)*x 0 + (876405741/2000000000 : ℝ)*x 1 + (4382026173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (728138001/2000000000 : ℝ)^5199 ≤ (5683102121783/20000000000000 : ℝ)^4175 := by
    have hnat : (728138001 : ℕ)^5199*20000000000000^4175 ≤ 5683102121783^4175*2000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      728138001 2000000000 5683102121783 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876405741/2000000000 : ℝ)^5199 ≤ (11185080489/31250000000 : ℝ)^4175 := by
    have hnat : (876405741 : ℕ)^5199*31250000000^4175 ≤ 11185080489^4175*2000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876405741 2000000000 11185080489 31250000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4382026173/10000000000 : ℝ)^5199 ≤ (1431689272441/4000000000000 : ℝ)^4175 := by
    have hnat : (4382026173 : ℕ)^5199*4000000000000^4175 ≤ 1431689272441^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382026173 10000000000 1431689272441 4000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(728138001/2000000000 : ℝ), (876405741/2000000000 : ℝ), (4382026173/10000000000 : ℝ)] ![(5683102121783/20000000000000 : ℝ), (11185080489/31250000000 : ℝ), (1431689272441/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(728138001/2000000000 : ℝ)|^5199 ≤ (5683102121783/20000000000000 : ℝ)^4175
        have hw : |(728138001/2000000000 : ℝ)|=(728138001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(876405741/2000000000 : ℝ)|^5199 ≤ (11185080489/31250000000 : ℝ)^4175
        have hw : |(876405741/2000000000 : ℝ)|=(876405741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4382026173/10000000000 : ℝ)|^5199 ≤ (1431689272441/4000000000000 : ℝ)^4175
        have hw : |(4382026173/10000000000 : ℝ)|=(4382026173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1697_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3437/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66631/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(3631/6250 : ℝ) ∧ (10131/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (18047/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3437/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9899/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3437/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9899/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3437/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9899/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3437/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9899/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3437/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9899/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3437/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9899/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9899/100000 : ℝ) ^ (5191/1024 : ℝ) ≤ (202420742129953/25000000000000000000 : ℝ) := by
    have hpowers : (9899/100000 : ℝ)^5191 ≤ (202420742129953/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9899 : ℕ)^5191*25000000000000000000^1024 ≤ 202420742129953^1024*100000^5191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9899 100000 202420742129953 25000000000000000000 5191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9899/100000 : ℝ)) (X := (202420742129953/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3437/20000 : ℝ) ^ (5191/1024 : ℝ) ≤ (13265268913682901/100000000000000000000 : ℝ) := by
    have hpowers : (3437/20000 : ℝ)^5191 ≤ (13265268913682901/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3437 : ℕ)^5191*100000000000000000000^1024 ≤ 13265268913682901^1024*20000^5191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3437 20000 13265268913682901 100000000000000000000 5191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3437/20000 : ℝ)) (X := (13265268913682901/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500202420742129953/12500000000000000000 : ℝ) ≤ (10000031944132957/10000000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (12500202420742129953/12500000000000000000 : ℝ)^1024 ≤ (10000031944132957/10000000000000000 : ℝ)^5191 := by
      have hnat : (12500202420742129953 : ℕ)^1024*10000000000000000^5191 ≤ 10000031944132957^5191*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500202420742129953 12500000000000000000 10000031944132957 10000000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000031944132957/10000000000000000 : ℝ)) (X := (12500202420742129953/12500000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100014074951882202713/100000000000000000000 : ℝ) ≤ (1000027763314557/1000000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (100014074951882202713/100000000000000000000 : ℝ)^1024 ≤ (1000027763314557/1000000000000000 : ℝ)^5191 := by
      have hnat : (100014074951882202713 : ℕ)^1024*1000000000000000^5191 ≤ 1000027763314557^5191*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100014074951882202713 100000000000000000000 1000027763314557 1000000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000027763314557/1000000000000000 : ℝ)) (X := (100014074951882202713/100000000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50013265268913682901/50000000000000000000 : ℝ) ≤ (10000523322158183/10000000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (50013265268913682901/50000000000000000000 : ℝ)^1024 ≤ (10000523322158183/10000000000000000 : ℝ)^5191 := by
      have hnat : (50013265268913682901 : ℕ)^1024*10000000000000000^5191 ≤ 10000523322158183^5191*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013265268913682901 50000000000000000000 10000523322158183 10000000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000523322158183/10000000000000000 : ℝ)) (X := (50013265268913682901/50000000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(202420742129953/25000000000000000000 : ℝ) ≤ ((4553460537117563283/4553750000000000000 : ℝ)+2*(245689012613/728600000000000 : ℝ)*(9899/100000 : ℝ))^(5191/1024 : ℝ) := by
    rw [show (4553460537117563283/4553750000000000000 : ℝ)+2*(245689012613/728600000000000 : ℝ)*(9899/100000 : ℝ)=(10000031944132957/10000000000000000 : ℝ) by norm_num, show 1+2*(202420742129953/25000000000000000000 : ℝ)=(12500202420742129953/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13265268913682901/100000000000000000000 : ℝ)+(202420742129953/25000000000000000000 : ℝ) ≤ ((4553460537117563283/4553750000000000000 : ℝ)+(245689012613/728600000000000 : ℝ)*((3437/20000 : ℝ)+(9899/100000 : ℝ)))^(5191/1024 : ℝ) := by
    rw [show (4553460537117563283/4553750000000000000 : ℝ)+(245689012613/728600000000000 : ℝ)*((3437/20000 : ℝ)+(9899/100000 : ℝ))=(1000027763314557/1000000000000000 : ℝ) by norm_num, show 1+(13265268913682901/100000000000000000000 : ℝ)+(202420742129953/25000000000000000000 : ℝ)=(100014074951882202713/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13265268913682901/100000000000000000000 : ℝ) ≤ ((4553460537117563283/4553750000000000000 : ℝ)+2*(245689012613/728600000000000 : ℝ)*(3437/20000 : ℝ))^(5191/1024 : ℝ) := by
    rw [show (4553460537117563283/4553750000000000000 : ℝ)+2*(245689012613/728600000000000 : ℝ)*(3437/20000 : ℝ)=(10000523322158183/10000000000000000 : ℝ) by norm_num, show 1+2*(13265268913682901/100000000000000000000 : ℝ)=(50013265268913682901/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4553460537117563283/4553750000000000000 : ℝ)*(X 1 0+X 2 0)+(245689012613/728600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (9899/100000 : ℝ)) (hi := (3437/20000 : ℝ)) (c := (4553460537117563283/4553750000000000000 : ℝ)) (alpha := (245689012613/728600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4553460537117563283/4553750000000000000 : ℝ)*(X 0 1+X 2 1)+(245689012613/728600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (9899/100000 : ℝ)) (hi := (3437/20000 : ℝ)) (c := (4553460537117563283/4553750000000000000 : ℝ)) (alpha := (245689012613/728600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4553460537117563283/4553750000000000000 : ℝ)*(X 0 2+X 1 2)+(245689012613/728600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (9899/100000 : ℝ)) (hi := (3437/20000 : ℝ)) (c := (4553460537117563283/4553750000000000000 : ℝ)) (alpha := (245689012613/728600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1131433527/10000000000 : ℝ)*X 0 0+(542421047/1000000000 : ℝ)*X 0 1+(216968413/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612948187/5000000000 : ℝ)*X 1 0+(-176659129/1250000000 : ℝ)*X 1 1+(5424210309/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5225896363/10000000000 : ℝ)*X 2 0+(542421033/1000000000 : ℝ)*X 2 1+(-706636509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4505135851/10000000000 : ℝ)*X 0 0+(123510561/312500000 : ℝ)*X 0 1+(1976168947/5000000000 : ℝ)*X 0 2+(4505135851/10000000000 : ℝ)*X 1 0+(123510561/312500000 : ℝ)*X 1 1+(1976168947/5000000000 : ℝ)*X 1 2+(4505135851/10000000000 : ℝ)*X 2 0+(123510561/312500000 : ℝ)*X 2 1+(1976168947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1810351993/10000000000 : ℝ)*X 0 0+(2588370531/5000000000 : ℝ)*X 0 1+(5176740971/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5394255431/10000000000 : ℝ)*X 1 0+(-304314487/2000000000 : ℝ)*X 1 1+(5176741031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5394255491/10000000000 : ℝ)*X 2 0+(2588370479/5000000000 : ℝ)*X 2 1+(-380393113/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((744685499/2000000000 : ℝ)*X 0 0+(542792927/1250000000 : ℝ)*X 0 1+(868468679/2000000000 : ℝ)*X 0 2+(744685499/2000000000 : ℝ)*X 1 0+(542792927/1250000000 : ℝ)*X 1 1+(868468679/2000000000 : ℝ)*X 1 2+(744685499/2000000000 : ℝ)*X 2 0+(542792927/1250000000 : ℝ)*X 2 1+(868468679/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-832272041/5000000000 : ℝ)*X 0 0+(1248692841/2500000000 : ℝ)*X 0 1+(273374641/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5196464847/10000000000 : ℝ)*X 1 0+(-1393516053/10000000000 : ℝ)*X 1 1+(2733746399/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1299116597/2500000000 : ℝ)*X 2 0+(2733745833/5000000000 : ℝ)*X 2 1+(-139351551/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((463684553/1000000000 : ℝ)*X 0 0+(1941971601/5000000000 : ℝ)*X 0 1+(388394973/1000000000 : ℝ)*X 0 2+(463684553/1000000000 : ℝ)*X 1 0+(1941971601/5000000000 : ℝ)*X 1 1+(388394973/1000000000 : ℝ)*X 1 2+(463684553/1000000000 : ℝ)*X 2 0+(1941971601/5000000000 : ℝ)*X 2 1+(388394973/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1272189541/10000000000 : ℝ)*X 0 0+(1399325597/2500000000 : ℝ)*X 0 1+(5151492563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((676432589/1250000000 : ℝ)*X 1 0+(-1532157953/10000000000 : ℝ)*X 1 1+(1287873281/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1082292337/2000000000 : ℝ)*X 2 0+(1287872959/2500000000 : ℝ)*X 2 1+(-1532158361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((728138001/2000000000 : ℝ)*X 0 0+(876405741/2000000000 : ℝ)*X 0 1+(4382026173/10000000000 : ℝ)*X 0 2+(728138001/2000000000 : ℝ)*X 1 0+(876405741/2000000000 : ℝ)*X 1 1+(4382026173/10000000000 : ℝ)*X 1 2+(728138001/2000000000 : ℝ)*X 2 0+(876405741/2000000000 : ℝ)*X 2 1+(4382026173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66631/100000 : ℝ) ≤ (-18962966847550196442559526509203/28460937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (174089/50000000000000 : ℝ)*(upper0) + (3520391/100000000000000 : ℝ)*(lower2) + (195043/100000000000000 : ℝ)*(lower3) + (165442402858747/12500000000000 : ℝ)*(major0) + (165442402858747/12500000000000 : ℝ)*(major1) + (165442402858747/12500000000000 : ℝ)*(major2) + (10175657/100000000000000 : ℝ)*(sp1) + (504976963/100000000000000 : ℝ)*(sp2) + (3155369/4000000000000 : ℝ)*(sp3) + (493784185151731/25000000000000 : ℝ)*(sp4) + (987568576696353/50000000000000 : ℝ)*(sp5) + (1975136658591401/100000000000000 : ℝ)*(sp6) + (347075276163243/50000000000000 : ℝ)*(sp7) + (422961439/100000000000000 : ℝ)*(sp8) + (694150631210711/100000000000000 : ℝ)*(f.failure) + (493784290892091/25000000000000 : ℝ)*(f.sum) + (43412540612081/18215000000000000000000000000 : ℝ)*base66 + (133251839188592651/56921875000000000000000000000000 : ℝ)*base67 + (156591866005905151/56921875000000000000000000000000 : ℝ)*base69 + (38590078833370819/14230468750000000000000000000000 : ℝ)*base71 + (32864348767193/9107500000000000000000000000 : ℝ)*base74 + (25355267434632263/28460937500000000000000000000000 : ℝ)*base75 + (76313335280722931/14230468750000000000000000000000 : ℝ)*base78 + (856857720445032349/56921875000000000000000000000000 : ℝ)*base80 + (37979885598417/9107500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (22586809/10000000000000000000000 : ℝ)*base89 + (22586809/10000000000000000000000 : ℝ)*base91 + (22586809/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (3631/6250 : ℝ) ≤ (26456728608871085240862187267143/45537500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54477/2500000000000 : ℝ)*(upper3) + (3580183/100000000000000 : ℝ)*(upper4) + (3171131/100000000000000 : ℝ)*(lower5) + (284918354129307/20000000000000 : ℝ)*(major0) + (284918354129307/20000000000000 : ℝ)*(major1) + (284918354129307/20000000000000 : ℝ)*(major2) + (2082667463976337/100000000000000 : ℝ)*(sp0) + (2082666190632473/100000000000000 : ℝ)*(sp1) + (416533612252957/20000000000000 : ℝ)*(sp2) + (747148902893611/100000000000000 : ℝ)*(sp3) + (18482241/100000000000000 : ℝ)*(sp6) + (60218527/20000000000000 : ℝ)*(sp7) + (615770689/100000000000000 : ℝ)*(sp8) + (944557277/50000000000000 : ℝ)*(sp9) + (373574601993123/50000000000000 : ℝ)*(f.failure) + (1041334039873513/50000000000000 : ℝ)*(f.sum) + (17516541851863/7286000000000000000000000000 : ℝ)*base66 + (523073053680528631/91075000000000000000000000000000 : ℝ)*base67 + (275678334471421369/91075000000000000000000000000000 : ℝ)*base70 + (633854438903071369/91075000000000000000000000000000 : ℝ)*base72 + (63305758183667/7286000000000000000000000000 : ℝ)*base73 + (665817563706221369/91075000000000000000000000000000 : ℝ)*base76 + (258377363900021369/91075000000000000000000000000000 : ℝ)*base78 + (118048162327878631/91075000000000000000000000000000 : ℝ)*base79 + (2469573398951/7286000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (48216237/5000000000000000000000 : ℝ)*base89 + (48216237/5000000000000000000000 : ℝ)*base91 + (48216237/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (10131/12500 : ℝ) ≤ (2883471301067688326836966585623/3557617187500000000000000000000 : ℝ) := by norm_num
    linear_combination (42699859/25000000000000 : ℝ)*(upper0) + (63159537/50000000000000 : ℝ)*(lower1) + (244018853/50000000000000 : ℝ)*(lower3) + (8496273/12500000000000 : ℝ)*(upper4) + (181496411861497/12500000000000 : ℝ)*(major0) + (181496411861497/12500000000000 : ℝ)*(major1) + (181496411861497/12500000000000 : ℝ)*(major2) + (323127511/6250000000000 : ℝ)*(sp0) + (10958298231/12500000000000 : ℝ)*(sp1) + (9934674327/25000000000000 : ℝ)*(sp3) + (2115411722342561/100000000000000 : ℝ)*(sp8) + (264416153249611/12500000000000 : ℝ)*(sp9) + (132213555773921/6250000000000 : ℝ)*(sp10) + (76146908056049/10000000000000 : ℝ)*(sp11) + (380754409628899/50000000000000 : ℝ)*(f.failure) + (132213555773921/6250000000000 : ℝ)*(f.sum) + (21790955098483/9107500000000000000000000000 : ℝ)*base66 + (517818220404129099/56921875000000000000000000000000 : ℝ)*base68 + (528741423025004099/56921875000000000000000000000000 : ℝ)*base70 + (794049946319254099/56921875000000000000000000000000 : ℝ)*base72 + (3438966456219/1138437500000000000000000000 : ℝ)*base73 + (519166619249191599/56921875000000000000000000000000 : ℝ)*base76 + (172688839413629099/56921875000000000000000000000000 : ℝ)*base78 + (79588786560941599/56921875000000000000000000000000 : ℝ)*base80 + (7744011773321/1138437500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (43948781/5000000000000000000000 : ℝ)*base89 + (43948781/5000000000000000000000 : ℝ)*base91 + (43948781/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-18047/20000 : ℝ) ≤ (-51362215879463128060074785524533/56921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9306197/25000000000000 : ℝ)*(lower0) + (23446341/20000000000000 : ℝ)*(lower2) + (38260943/20000000000000 : ℝ)*(upper3) + (1499817122513959/100000000000000 : ℝ)*(major0) + (1499817122513959/100000000000000 : ℝ)*(major1) + (1499817122513959/100000000000000 : ℝ)*(major2) + (317373753/100000000000000 : ℝ)*(sp0) + (29357528771/100000000000000 : ℝ)*(sp5) + (44034522379/50000000000000 : ℝ)*(sp6) + (708445327/4000000000000 : ℝ)*(sp7) + (1121554615944179/50000000000000 : ℝ)*(sp12) + (112154009586667/5000000000000 : ℝ)*(sp13) + (2243021480217353/100000000000000 : ℝ)*(sp14) + (786584592980009/100000000000000 : ℝ)*(sp15) + (157320460822637/20000000000000 : ℝ)*(f.failure) + (2243109549262111/100000000000000 : ℝ)*(f.sum) + (4558856980363/36430000000000000000000000000 : ℝ)*base66 + (663902876809161147/455375000000000000000000000000000 : ℝ)*base67 + (1907026990023411147/455375000000000000000000000000000 : ℝ)*base69 + (654875936289661147/455375000000000000000000000000000 : ℝ)*base71 + (796579554316667/36430000000000000000000000000 : ℝ)*base73 + (240183368295161147/455375000000000000000000000000000 : ℝ)*base75 + (1121925638596088853/455375000000000000000000000000000 : ℝ)*base78 + (3282201905122411147/455375000000000000000000000000000 : ℝ)*base79 + (183606338134677/36430000000000000000000000000 : ℝ)*base81 + (19211203/2000000000000000000000 : ℝ)*base89 + (19211203/2000000000000000000000 : ℝ)*base91 + (19211203/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1697_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3437/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66631/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(3631/6250 : ℝ) else (10131/12500 : ℝ) ≤ X j i ∧ X j i ≤ (18047/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1697_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1697_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17203/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9883/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66631/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(3631/6250 : ℝ) else (10131/12500 : ℝ) ≤ X j i ∧ X j i ≤ (18047/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1697_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1697_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1697_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17203/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9883/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66631/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(3631/6250 : ℝ) else (10131/12500 : ℝ) ≤ X j i ∧ X j i ≤ (18047/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1697_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
