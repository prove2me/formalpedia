-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1378_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:22:47.187683+00:00
-- url     : https://prove2.me/submissions/1ed11e8c-8535-40d3-bdca-9e281dbbae92

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
theorem support_rectangle_w1378_s6_0 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-50331773/250000000 : ℝ)*x 0 + (2705428093/5000000000 : ℝ)*x 1 + (5245643701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50331773/250000000 : ℝ)^2169 ≤ (6134560759809/50000000000000 : ℝ)^1657 := by
    have hnat : (50331773 : ℕ)^2169*50000000000000^1657 ≤ 6134560759809^1657*250000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50331773 250000000 6134560759809 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705428093/5000000000 : ℝ)^2169 ≤ (1118889719821/2500000000000 : ℝ)^1657 := by
    have hnat : (2705428093 : ℕ)^2169*2500000000000^1657 ≤ 1118889719821^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705428093 5000000000 1118889719821 2500000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245643701/10000000000 : ℝ)^2169 ≤ (21487644840109/50000000000000 : ℝ)^1657 := by
    have hnat : (5245643701 : ℕ)^2169*50000000000000^1657 ≤ 21487644840109^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245643701 10000000000 21487644840109 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50331773/250000000 : ℝ), (2705428093/5000000000 : ℝ), (5245643701/10000000000 : ℝ)] ![(6134560759809/50000000000000 : ℝ), (1118889719821/2500000000000 : ℝ), (21487644840109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50331773/250000000 : ℝ)|^2169 ≤ (6134560759809/50000000000000 : ℝ)^1657
        have hw : |(-50331773/250000000 : ℝ)|=(50331773/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705428093/5000000000 : ℝ)|^2169 ≤ (1118889719821/2500000000000 : ℝ)^1657
        have hw : |(2705428093/5000000000 : ℝ)|=(2705428093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245643701/10000000000 : ℝ)|^2169 ≤ (21487644840109/50000000000000 : ℝ)^1657
        have hw : |(5245643701/10000000000 : ℝ)|=(5245643701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s6_1 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534834919/1000000000 : ℝ)*x 0 + (-2097420381/10000000000 : ℝ)*x 1 + (5245643751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534834919/1000000000 : ℝ)^2169 ≤ (22040010392807/50000000000000 : ℝ)^1657 := by
    have hnat : (534834919 : ℕ)^2169*50000000000000^1657 ≤ 22040010392807^1657*1000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534834919 1000000000 22040010392807 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2097420381/10000000000 : ℝ)^2169 ≤ (12944688975457/100000000000000 : ℝ)^1657 := by
    have hnat : (2097420381 : ℕ)^2169*100000000000000^1657 ≤ 12944688975457^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097420381 10000000000 12944688975457 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245643751/10000000000 : ℝ)^2169 ≤ (42975290216419/100000000000000 : ℝ)^1657 := by
    have hnat : (5245643751 : ℕ)^2169*100000000000000^1657 ≤ 42975290216419^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245643751 10000000000 42975290216419 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534834919/1000000000 : ℝ), (-2097420381/10000000000 : ℝ), (5245643751/10000000000 : ℝ)] ![(22040010392807/50000000000000 : ℝ), (12944688975457/100000000000000 : ℝ), (42975290216419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534834919/1000000000 : ℝ)|^2169 ≤ (22040010392807/50000000000000 : ℝ)^1657
        have hw : |(534834919/1000000000 : ℝ)|=(534834919/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2097420381/10000000000 : ℝ)|^2169 ≤ (12944688975457/100000000000000 : ℝ)^1657
        have hw : |(-2097420381/10000000000 : ℝ)|=(2097420381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245643751/10000000000 : ℝ)|^2169 ≤ (42975290216419/100000000000000 : ℝ)^1657
        have hw : |(5245643751/10000000000 : ℝ)|=(5245643751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s6_2 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337087349/2500000000 : ℝ)*x 0 + (5245643657/10000000000 : ℝ)*x 1 + (-2097420231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337087349/2500000000 : ℝ)^2169 ≤ (8816004601607/20000000000000 : ℝ)^1657 := by
    have hnat : (1337087349 : ℕ)^2169*20000000000000^1657 ≤ 8816004601607^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337087349 2500000000 8816004601607 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245643657/10000000000 : ℝ)^2169 ≤ (21487644604181/50000000000000 : ℝ)^1657 := by
    have hnat : (5245643657 : ℕ)^2169*50000000000000^1657 ≤ 21487644604181^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245643657 10000000000 21487644604181 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2097420231/10000000000 : ℝ)^2169 ≤ (12944687763647/100000000000000 : ℝ)^1657 := by
    have hnat : (2097420231 : ℕ)^2169*100000000000000^1657 ≤ 12944687763647^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097420231 10000000000 12944687763647 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337087349/2500000000 : ℝ), (5245643657/10000000000 : ℝ), (-2097420231/10000000000 : ℝ)] ![(8816004601607/20000000000000 : ℝ), (21487644604181/50000000000000 : ℝ), (12944687763647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337087349/2500000000 : ℝ)|^2169 ≤ (8816004601607/20000000000000 : ℝ)^1657
        have hw : |(1337087349/2500000000 : ℝ)|=(1337087349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245643657/10000000000 : ℝ)|^2169 ≤ (21487644604181/50000000000000 : ℝ)^1657
        have hw : |(5245643657/10000000000 : ℝ)|=(5245643657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2097420231/10000000000 : ℝ)|^2169 ≤ (12944687763647/100000000000000 : ℝ)^1657
        have hw : |(-2097420231/10000000000 : ℝ)|=(2097420231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s6_3 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (215864649/500000000 : ℝ)*x 0 + (2072598737/5000000000 : ℝ)*x 1 + (2247969967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215864649/500000000 : ℝ)^2169 ≤ (260186509097/781250000000 : ℝ)^1657 := by
    have hnat : (215864649 : ℕ)^2169*781250000000^1657 ≤ 260186509097^1657*500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215864649 500000000 260186509097 781250000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072598737/5000000000 : ℝ)^2169 ≤ (15788457565199/50000000000000 : ℝ)^1657 := by
    have hnat : (2072598737 : ℕ)^2169*50000000000000^1657 ≤ 15788457565199^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072598737 5000000000 15788457565199 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247969967/5000000000 : ℝ)^2169 ≤ (8779802921567/25000000000000 : ℝ)^1657 := by
    have hnat : (2247969967 : ℕ)^2169*25000000000000^1657 ≤ 8779802921567^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247969967 5000000000 8779802921567 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215864649/500000000 : ℝ), (2072598737/5000000000 : ℝ), (2247969967/5000000000 : ℝ)] ![(260186509097/781250000000 : ℝ), (15788457565199/50000000000000 : ℝ), (8779802921567/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215864649/500000000 : ℝ)|^2169 ≤ (260186509097/781250000000 : ℝ)^1657
        have hw : |(215864649/500000000 : ℝ)|=(215864649/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2072598737/5000000000 : ℝ)|^2169 ≤ (15788457565199/50000000000000 : ℝ)^1657
        have hw : |(2072598737/5000000000 : ℝ)|=(2072598737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247969967/5000000000 : ℝ)|^2169 ≤ (8779802921567/25000000000000 : ℝ)^1657
        have hw : |(2247969967/5000000000 : ℝ)|=(2247969967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s6_4 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-402656521/2000000000 : ℝ)*x 0 + (5246237041/10000000000 : ℝ)*x 1 + (2705129937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402656521/2000000000 : ℝ)^2169 ≤ (12269214732813/100000000000000 : ℝ)^1657 := by
    have hnat : (402656521 : ℕ)^2169*100000000000000^1657 ≤ 12269214732813^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402656521 2000000000 12269214732813 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246237041/10000000000 : ℝ)^2169 ≤ (42981652773413/100000000000000 : ℝ)^1657 := by
    have hnat : (5246237041 : ℕ)^2169*100000000000000^1657 ≤ 42981652773413^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246237041 10000000000 42981652773413 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705129937/5000000000 : ℝ)^2169 ≤ (7159861197/16000000000 : ℝ)^1657 := by
    have hnat : (2705129937 : ℕ)^2169*16000000000^1657 ≤ 7159861197^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705129937 5000000000 7159861197 16000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-402656521/2000000000 : ℝ), (5246237041/10000000000 : ℝ), (2705129937/5000000000 : ℝ)] ![(12269214732813/100000000000000 : ℝ), (42981652773413/100000000000000 : ℝ), (7159861197/16000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-402656521/2000000000 : ℝ)|^2169 ≤ (12269214732813/100000000000000 : ℝ)^1657
        have hw : |(-402656521/2000000000 : ℝ)|=(402656521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246237041/10000000000 : ℝ)|^2169 ≤ (42981652773413/100000000000000 : ℝ)^1657
        have hw : |(5246237041/10000000000 : ℝ)|=(5246237041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705129937/5000000000 : ℝ)|^2169 ≤ (7159861197/16000000000 : ℝ)^1657
        have hw : |(2705129937/5000000000 : ℝ)|=(2705129937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s6_5 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (33160143/62500000 : ℝ)*x 0 + (-193280403/1000000000 : ℝ)*x 1 + (1352565023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33160143/62500000 : ℝ)^2169 ≤ (21809820031843/50000000000000 : ℝ)^1657 := by
    have hnat : (33160143 : ℕ)^2169*50000000000000^1657 ≤ 21809820031843^1657*62500000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33160143 62500000 21809820031843 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193280403/1000000000 : ℝ)^2169 ≤ (1163122507551/10000000000000 : ℝ)^1657 := by
    have hnat : (193280403 : ℕ)^2169*10000000000000^1657 ≤ 1163122507551^1657*1000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193280403 1000000000 1163122507551 10000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352565023/2500000000 : ℝ)^2169 ≤ (44749134841511/100000000000000 : ℝ)^1657 := by
    have hnat : (1352565023 : ℕ)^2169*100000000000000^1657 ≤ 44749134841511^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352565023 2500000000 44749134841511 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33160143/62500000 : ℝ), (-193280403/1000000000 : ℝ), (1352565023/2500000000 : ℝ)] ![(21809820031843/50000000000000 : ℝ), (1163122507551/10000000000000 : ℝ), (44749134841511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33160143/62500000 : ℝ)|^2169 ≤ (21809820031843/50000000000000 : ℝ)^1657
        have hw : |(33160143/62500000 : ℝ)|=(33160143/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-193280403/1000000000 : ℝ)|^2169 ≤ (1163122507551/10000000000000 : ℝ)^1657
        have hw : |(-193280403/1000000000 : ℝ)|=(193280403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352565023/2500000000 : ℝ)|^2169 ≤ (44749134841511/100000000000000 : ℝ)^1657
        have hw : |(1352565023/2500000000 : ℝ)|=(1352565023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s6_6 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305622851/10000000000 : ℝ)*x 0 + (5410260121/10000000000 : ℝ)*x 1 + (-193280403/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305622851/10000000000 : ℝ)^2169 ≤ (10904909937899/25000000000000 : ℝ)^1657 := by
    have hnat : (5305622851 : ℕ)^2169*25000000000000^1657 ≤ 10904909937899^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305622851 10000000000 10904909937899 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410260121/10000000000 : ℝ)^2169 ≤ (44749135155491/100000000000000 : ℝ)^1657 := by
    have hnat : (5410260121 : ℕ)^2169*100000000000000^1657 ≤ 44749135155491^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410260121 10000000000 44749135155491 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (193280403/1000000000 : ℝ)^2169 ≤ (1163122507551/10000000000000 : ℝ)^1657 := by
    have hnat : (193280403 : ℕ)^2169*10000000000000^1657 ≤ 1163122507551^1657*1000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193280403 1000000000 1163122507551 10000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305622851/10000000000 : ℝ), (5410260121/10000000000 : ℝ), (-193280403/1000000000 : ℝ)] ![(10904909937899/25000000000000 : ℝ), (44749135155491/100000000000000 : ℝ), (1163122507551/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305622851/10000000000 : ℝ)|^2169 ≤ (10904909937899/25000000000000 : ℝ)^1657
        have hw : |(5305622851/10000000000 : ℝ)|=(5305622851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410260121/10000000000 : ℝ)|^2169 ≤ (44749135155491/100000000000000 : ℝ)^1657
        have hw : |(5410260121/10000000000 : ℝ)|=(5410260121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-193280403/1000000000 : ℝ)|^2169 ≤ (1163122507551/10000000000000 : ℝ)^1657
        have hw : |(-193280403/1000000000 : ℝ)|=(193280403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s6_7 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4317318107/10000000000 : ℝ)*x 0 + (4494680379/10000000000 : ℝ)*x 1 + (103661587/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317318107/10000000000 : ℝ)^2169 ≤ (8326031722067/25000000000000 : ℝ)^1657 := by
    have hnat : (4317318107 : ℕ)^2169*25000000000000^1657 ≤ 8326031722067^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317318107 10000000000 8326031722067 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494680379/10000000000 : ℝ)^2169 ≤ (17553166676803/50000000000000 : ℝ)^1657 := by
    have hnat : (4494680379 : ℕ)^2169*50000000000000^1657 ≤ 17553166676803^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494680379 10000000000 17553166676803 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103661587/250000000 : ℝ)^2169 ≤ (631790794693/2000000000000 : ℝ)^1657 := by
    have hnat : (103661587 : ℕ)^2169*2000000000000^1657 ≤ 631790794693^1657*250000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103661587 250000000 631790794693 2000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317318107/10000000000 : ℝ), (4494680379/10000000000 : ℝ), (103661587/250000000 : ℝ)] ![(8326031722067/25000000000000 : ℝ), (17553166676803/50000000000000 : ℝ), (631790794693/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317318107/10000000000 : ℝ)|^2169 ≤ (8326031722067/25000000000000 : ℝ)^1657
        have hw : |(4317318107/10000000000 : ℝ)|=(4317318107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494680379/10000000000 : ℝ)|^2169 ≤ (17553166676803/50000000000000 : ℝ)^1657
        have hw : |(4494680379/10000000000 : ℝ)|=(4494680379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103661587/250000000 : ℝ)|^2169 ≤ (631790794693/2000000000000 : ℝ)^1657
        have hw : |(103661587/250000000 : ℝ)|=(103661587/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1378_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11231/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14729/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2947/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2947/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2947/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2947/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2947/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2947/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5613/50000 : ℝ) ^ (4337/1024 : ℝ) ≤ (4746124588525107/50000000000000000000 : ℝ) := by
    have hpowers : (5613/50000 : ℝ)^4337 ≤ (4746124588525107/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5613 : ℕ)^4337*50000000000000000000^1024 ≤ 4746124588525107^1024*50000^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5613 50000 4746124588525107 50000000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5613/50000 : ℝ)) (X := (4746124588525107/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2947/20000 : ℝ) ^ (4337/1024 : ℝ) ≤ (1877372638996201/6250000000000000000 : ℝ) := by
    have hpowers : (2947/20000 : ℝ)^4337 ≤ (1877372638996201/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2947 : ℕ)^4337*6250000000000000000^1024 ≤ 1877372638996201^1024*20000^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2947 20000 1877372638996201 6250000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2947/20000 : ℝ)) (X := (1877372638996201/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004746124588525107/25000000000000000000 : ℝ) ≤ (10000448206521971/10000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (25004746124588525107/25000000000000000000 : ℝ)^1024 ≤ (10000448206521971/10000000000000000 : ℝ)^4337 := by
      have hnat : (25004746124588525107 : ℕ)^1024*10000000000000000^4337 ≤ 10000448206521971^4337*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004746124588525107 25000000000000000000 10000448206521971 10000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000448206521971/10000000000000000 : ℝ)) (X := (25004746124588525107/25000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003953021140098943/10000000000000000000 : ℝ) ≤ (5000466599333869/5000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (10003953021140098943/10000000000000000000 : ℝ)^1024 ≤ (5000466599333869/5000000000000000 : ℝ)^4337 := by
      have hnat : (10003953021140098943 : ℕ)^1024*5000000000000000^4337 ≤ 5000466599333869^4337*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003953021140098943 10000000000000000000 5000466599333869 5000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000466599333869/5000000000000000 : ℝ)) (X := (10003953021140098943/10000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126877372638996201/3125000000000000000 : ℝ) ≤ (2000283638162701/2000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (3126877372638996201/3125000000000000000 : ℝ)^1024 ≤ (2000283638162701/2000000000000000 : ℝ)^4337 := by
      have hnat : (3126877372638996201 : ℕ)^1024*2000000000000000^4337 ≤ 2000283638162701^4337*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126877372638996201 3125000000000000000 2000283638162701 2000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000283638162701/2000000000000000 : ℝ)) (X := (3126877372638996201/3125000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4746124588525107/50000000000000000000 : ℝ) ≤ ((7016136742605767111/7018000000000000000 : ℝ)+2*(484992145767/350900000000000 : ℝ)*(5613/50000 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (7016136742605767111/7018000000000000000 : ℝ)+2*(484992145767/350900000000000 : ℝ)*(5613/50000 : ℝ)=(10000448206521971/10000000000000000 : ℝ) by norm_num, show 1+2*(4746124588525107/50000000000000000000 : ℝ)=(25004746124588525107/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1877372638996201/6250000000000000000 : ℝ)+(4746124588525107/50000000000000000000 : ℝ) ≤ ((7016136742605767111/7018000000000000000 : ℝ)+(484992145767/350900000000000 : ℝ)*((2947/20000 : ℝ)+(5613/50000 : ℝ)))^(4337/1024 : ℝ) := by
    rw [show (7016136742605767111/7018000000000000000 : ℝ)+(484992145767/350900000000000 : ℝ)*((2947/20000 : ℝ)+(5613/50000 : ℝ))=(5000466599333869/5000000000000000 : ℝ) by norm_num, show 1+(1877372638996201/6250000000000000000 : ℝ)+(4746124588525107/50000000000000000000 : ℝ)=(10003953021140098943/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1877372638996201/6250000000000000000 : ℝ) ≤ ((7016136742605767111/7018000000000000000 : ℝ)+2*(484992145767/350900000000000 : ℝ)*(2947/20000 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (7016136742605767111/7018000000000000000 : ℝ)+2*(484992145767/350900000000000 : ℝ)*(2947/20000 : ℝ)=(2000283638162701/2000000000000000 : ℝ) by norm_num, show 1+2*(1877372638996201/6250000000000000000 : ℝ)=(3126877372638996201/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7016136742605767111/7018000000000000000 : ℝ)*(X 1 0+X 2 0)+(484992145767/350900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (2947/20000 : ℝ)) (c := (7016136742605767111/7018000000000000000 : ℝ)) (alpha := (484992145767/350900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7016136742605767111/7018000000000000000 : ℝ)*(X 0 1+X 2 1)+(484992145767/350900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (2947/20000 : ℝ)) (c := (7016136742605767111/7018000000000000000 : ℝ)) (alpha := (484992145767/350900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7016136742605767111/7018000000000000000 : ℝ)*(X 0 2+X 1 2)+(484992145767/350900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (2947/20000 : ℝ)) (c := (7016136742605767111/7018000000000000000 : ℝ)) (alpha := (484992145767/350900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-50331773/250000000 : ℝ)*X 0 0+(2705428093/5000000000 : ℝ)*X 0 1+(5245643701/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534834919/1000000000 : ℝ)*X 1 0+(-2097420381/10000000000 : ℝ)*X 1 1+(5245643751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337087349/2500000000 : ℝ)*X 2 0+(5245643657/10000000000 : ℝ)*X 2 1+(-2097420231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((215864649/500000000 : ℝ)*X 0 0+(2072598737/5000000000 : ℝ)*X 0 1+(2247969967/5000000000 : ℝ)*X 0 2+(215864649/500000000 : ℝ)*X 1 0+(2072598737/5000000000 : ℝ)*X 1 1+(2247969967/5000000000 : ℝ)*X 1 2+(215864649/500000000 : ℝ)*X 2 0+(2072598737/5000000000 : ℝ)*X 2 1+(2247969967/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-402656521/2000000000 : ℝ)*X 0 0+(5246237041/10000000000 : ℝ)*X 0 1+(2705129937/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((33160143/62500000 : ℝ)*X 1 0+(-193280403/1000000000 : ℝ)*X 1 1+(1352565023/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305622851/10000000000 : ℝ)*X 2 0+(5410260121/10000000000 : ℝ)*X 2 1+(-193280403/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4317318107/10000000000 : ℝ)*X 0 0+(4494680379/10000000000 : ℝ)*X 0 1+(103661587/250000000 : ℝ)*X 0 2+(4317318107/10000000000 : ℝ)*X 1 0+(4494680379/10000000000 : ℝ)*X 1 1+(103661587/250000000 : ℝ)*X 1 2+(4317318107/10000000000 : ℝ)*X 2 0+(4494680379/10000000000 : ℝ)*X 2 1+(103661587/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1282831007364292069767/199375000000000000000000000 : ℝ) := by norm_num
    linear_combination (1256533373/100000000000000 : ℝ)*(base19) + (283935991/20000000000000 : ℝ)*(base23) + (37432467/100000000000000 : ℝ)*(lower2) + (59910197/50000000000000 : ℝ)*(upper3) + (295604819/100000000000000 : ℝ)*(upper5) + (2225995861948419/50000000000000 : ℝ)*(major0) + (2225995861948419/50000000000000 : ℝ)*(major1) + (2225995861948419/50000000000000 : ℝ)*(major2) + (3026416281389221/50000000000000 : ℝ)*(sp0) + (6052862156473379/100000000000000 : ℝ)*(sp1) + (1513215498331699/25000000000000 : ℝ)*(sp2) + (356388498232107/12500000000000 : ℝ)*(sp3) + (30850228309/100000000000000 : ℝ)*(sp4) + (11834454657/100000000000000 : ℝ)*(sp7) + (1425559910155757/50000000000000 : ℝ)*(f.failure) + (189151981656461/3125000000000 : ℝ)*(f.sum) + (51045616983/49843750000000000000000000 : ℝ)*base65 + (41785374791735681/31900000000000000000000000000000 : ℝ)*base68 + (270685073414664319/31900000000000000000000000000000 : ℝ)*base69 + (298247393812364319/31900000000000000000000000000000 : ℝ)*base71 + (1103155382913/797500000000000000000000000 : ℝ)*base73 + (32101359885235681/31900000000000000000000000000000 : ℝ)*base76 + (120053923440964319/31900000000000000000000000000000 : ℝ)*base77 + (27104901994635681/31900000000000000000000000000000 : ℝ)*base80 + (5777793632513/797500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (706837/2500000000000000000000 : ℝ)*base89 + (706837/2500000000000000000000 : ℝ)*base91 + (706837/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (778358425995116461171989273/175450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13471917/3125000000000 : ℝ)*(base19) + (656130523/100000000000000 : ℝ)*(base23) + (144563753/100000000000000 : ℝ)*(upper3) + (115888129/100000000000000 : ℝ)*(lower4) + (130738379/100000000000000 : ℝ)*(upper5) + (4484240842613819/100000000000000 : ℝ)*(major0) + (4484240842613819/100000000000000 : ℝ)*(major1) + (4484240842613819/100000000000000 : ℝ)*(major2) + (565584211/5000000000000 : ℝ)*(sp1) + (4067434747/25000000000000 : ℝ)*(sp2) + (3048354457745423/50000000000000 : ℝ)*(sp4) + (3048348586352641/50000000000000 : ℝ)*(sp5) + (1219338397924267/20000000000000 : ℝ)*(sp6) + (2871772621858297/100000000000000 : ℝ)*(sp7) + (2871772621858297/100000000000000 : ℝ)*(f.failure) + (3048354457745423/50000000000000 : ℝ)*(f.sum) + (199510787629/2193125000000000000000000000 : ℝ)*base66 + (3680859247359566909/701800000000000000000000000000000 : ℝ)*base67 + (5128222579427433091/701800000000000000000000000000000 : ℝ)*base70 + (2351133178677566909/701800000000000000000000000000000 : ℝ)*base71 + (15075529494469/8772500000000000000000000000 : ℝ)*base73 + (2112667865404566909/701800000000000000000000000000000 : ℝ)*base75 + (3676311679506166909/701800000000000000000000000000000 : ℝ)*base77 + (1500048054722566909/701800000000000000000000000000000 : ℝ)*base79 + (52916919008517/17545000000000000000000000000 : ℝ)*base82 + (30513023/5000000000000000000000 : ℝ)*base90 + (30513023/5000000000000000000000 : ℝ)*base92 + (30513023/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1378_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1378_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1378_s7_0 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1006638963/5000000000 : ℝ)*x 0 + (2705405439/5000000000 : ℝ)*x 1 + (5245684233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006638963/5000000000 : ℝ)^2169 ≤ (12269177407629/100000000000000 : ℝ)^1657 := by
    have hnat : (1006638963 : ℕ)^2169*100000000000000^1657 ≤ 12269177407629^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006638963 5000000000 12269177407629 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705405439/5000000000 : ℝ)^2169 ≤ (44755098232247/100000000000000 : ℝ)^1657 := by
    have hnat : (2705405439 : ℕ)^2169*100000000000000^1657 ≤ 44755098232247^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705405439 5000000000 44755098232247 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245684233/10000000000 : ℝ)^2169 ≤ (5371965543271/12500000000000 : ℝ)^1657 := by
    have hnat : (5245684233 : ℕ)^2169*12500000000000^1657 ≤ 5371965543271^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245684233 10000000000 5371965543271 12500000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1006638963/5000000000 : ℝ), (2705405439/5000000000 : ℝ), (5245684233/10000000000 : ℝ)] ![(12269177407629/100000000000000 : ℝ), (44755098232247/100000000000000 : ℝ), (5371965543271/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1006638963/5000000000 : ℝ)|^2169 ≤ (12269177407629/100000000000000 : ℝ)^1657
        have hw : |(-1006638963/5000000000 : ℝ)|=(1006638963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705405439/5000000000 : ℝ)|^2169 ≤ (44755098232247/100000000000000 : ℝ)^1657
        have hw : |(2705405439/5000000000 : ℝ)|=(2705405439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245684233/10000000000 : ℝ)|^2169 ≤ (5371965543271/12500000000000 : ℝ)^1657
        have hw : |(5245684233/10000000000 : ℝ)|=(5245684233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s7_1 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674168473/5000000000 : ℝ)*x 0 + (-524345781/2500000000 : ℝ)*x 1 + (655710517/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674168473/5000000000 : ℝ)^2169 ≤ (44079888691871/100000000000000 : ℝ)^1657 := by
    have hnat : (2674168473 : ℕ)^2169*100000000000000^1657 ≤ 44079888691871^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674168473 5000000000 44079888691871 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524345781/2500000000 : ℝ)^2169 ≤ (12944387986979/100000000000000 : ℝ)^1657 := by
    have hnat : (524345781 : ℕ)^2169*100000000000000^1657 ≤ 12944387986979^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524345781 2500000000 12944387986979 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655710517/1250000000 : ℝ)^2169 ≤ (42975723305937/100000000000000 : ℝ)^1657 := by
    have hnat : (655710517 : ℕ)^2169*100000000000000^1657 ≤ 42975723305937^1657*1250000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655710517 1250000000 42975723305937 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674168473/5000000000 : ℝ), (-524345781/2500000000 : ℝ), (655710517/1250000000 : ℝ)] ![(44079888691871/100000000000000 : ℝ), (12944387986979/100000000000000 : ℝ), (42975723305937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674168473/5000000000 : ℝ)|^2169 ≤ (44079888691871/100000000000000 : ℝ)^1657
        have hw : |(2674168473/5000000000 : ℝ)|=(2674168473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-524345781/2500000000 : ℝ)|^2169 ≤ (12944387986979/100000000000000 : ℝ)^1657
        have hw : |(-524345781/2500000000 : ℝ)|=(524345781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655710517/1250000000 : ℝ)|^2169 ≤ (42975723305937/100000000000000 : ℝ)^1657
        have hw : |(655710517/1250000000 : ℝ)|=(655710517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s7_2 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348337021/10000000000 : ℝ)*x 0 + (1311420833/2500000000 : ℝ)*x 1 + (-2097384091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348337021/10000000000 : ℝ)^2169 ≤ (11019972375251/25000000000000 : ℝ)^1657 := by
    have hnat : (5348337021 : ℕ)^2169*25000000000000^1657 ≤ 11019972375251^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348337021 10000000000 11019972375251 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311420833/2500000000 : ℝ)^2169 ≤ (8595142936763/20000000000000 : ℝ)^1657 := by
    have hnat : (1311420833 : ℕ)^2169*20000000000000^1657 ≤ 8595142936763^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311420833 2500000000 8595142936763 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2097384091/10000000000 : ℝ)^2169 ≤ (12944395799071/100000000000000 : ℝ)^1657 := by
    have hnat : (2097384091 : ℕ)^2169*100000000000000^1657 ≤ 12944395799071^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097384091 10000000000 12944395799071 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348337021/10000000000 : ℝ), (1311420833/2500000000 : ℝ), (-2097384091/10000000000 : ℝ)] ![(11019972375251/25000000000000 : ℝ), (8595142936763/20000000000000 : ℝ), (12944395799071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348337021/10000000000 : ℝ)|^2169 ≤ (11019972375251/25000000000000 : ℝ)^1657
        have hw : |(5348337021/10000000000 : ℝ)|=(5348337021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311420833/2500000000 : ℝ)|^2169 ≤ (8595142936763/20000000000000 : ℝ)^1657
        have hw : |(1311420833/2500000000 : ℝ)|=(1311420833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2097384091/10000000000 : ℝ)|^2169 ≤ (12944395799071/100000000000000 : ℝ)^1657
        have hw : |(-2097384091/10000000000 : ℝ)|=(2097384091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s7_3 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2158648533/5000000000 : ℝ)*x 0 + (4145284861/10000000000 : ℝ)*x 1 + (2247925339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158648533/5000000000 : ℝ)^2169 ≤ (6660782884683/20000000000000 : ℝ)^1657 := by
    have hnat : (2158648533 : ℕ)^2169*20000000000000^1657 ≤ 6660782884683^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158648533 5000000000 6660782884683 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4145284861/10000000000 : ℝ)^2169 ≤ (31577786514763/100000000000000 : ℝ)^1657 := by
    have hnat : (4145284861 : ℕ)^2169*100000000000000^1657 ≤ 31577786514763^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145284861 10000000000 31577786514763 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247925339/5000000000 : ℝ)^2169 ≤ (35118299050701/100000000000000 : ℝ)^1657 := by
    have hnat : (2247925339 : ℕ)^2169*100000000000000^1657 ≤ 35118299050701^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247925339 5000000000 35118299050701 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158648533/5000000000 : ℝ), (4145284861/10000000000 : ℝ), (2247925339/5000000000 : ℝ)] ![(6660782884683/20000000000000 : ℝ), (31577786514763/100000000000000 : ℝ), (35118299050701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158648533/5000000000 : ℝ)|^2169 ≤ (6660782884683/20000000000000 : ℝ)^1657
        have hw : |(2158648533/5000000000 : ℝ)|=(2158648533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4145284861/10000000000 : ℝ)|^2169 ≤ (31577786514763/100000000000000 : ℝ)^1657
        have hw : |(4145284861/10000000000 : ℝ)|=(4145284861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247925339/5000000000 : ℝ)|^2169 ≤ (35118299050701/100000000000000 : ℝ)^1657
        have hw : |(2247925339/5000000000 : ℝ)|=(2247925339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s7_4 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1006644651/5000000000 : ℝ)*x 0 + (1049255247/2000000000 : ℝ)*x 1 + (5410216117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006644651/5000000000 : ℝ)^2169 ≤ (490770726239/4000000000000 : ℝ)^1657 := by
    have hnat : (1006644651 : ℕ)^2169*4000000000000^1657 ≤ 490770726239^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006644651 5000000000 490770726239 4000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049255247/2000000000 : ℝ)^2169 ≤ (21491036552649/50000000000000 : ℝ)^1657 := by
    have hnat : (1049255247 : ℕ)^2169*50000000000000^1657 ≤ 21491036552649^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049255247 2000000000 21491036552649 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410216117/10000000000 : ℝ)^2169 ≤ (2237432936491/5000000000000 : ℝ)^1657 := by
    have hnat : (5410216117 : ℕ)^2169*5000000000000^1657 ≤ 2237432936491^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410216117 10000000000 2237432936491 5000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1006644651/5000000000 : ℝ), (1049255247/2000000000 : ℝ), (5410216117/10000000000 : ℝ)] ![(490770726239/4000000000000 : ℝ), (21491036552649/50000000000000 : ℝ), (2237432936491/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1006644651/5000000000 : ℝ)|^2169 ≤ (490770726239/4000000000000 : ℝ)^1657
        have hw : |(-1006644651/5000000000 : ℝ)|=(1006644651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049255247/2000000000 : ℝ)|^2169 ≤ (21491036552649/50000000000000 : ℝ)^1657
        have hw : |(1049255247/2000000000 : ℝ)|=(1049255247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410216117/10000000000 : ℝ)|^2169 ≤ (2237432936491/5000000000000 : ℝ)^1657
        have hw : |(5410216117/10000000000 : ℝ)|=(5410216117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s7_5 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305632343/10000000000 : ℝ)*x 0 + (-966425317/5000000000 : ℝ)*x 1 + (5410216779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305632343/10000000000 : ℝ)^2169 ≤ (21809870951059/50000000000000 : ℝ)^1657 := by
    have hnat : (5305632343 : ℕ)^2169*50000000000000^1657 ≤ 21809870951059^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305632343 10000000000 21809870951059 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (966425317/5000000000 : ℝ)^2169 ≤ (290789804707/2500000000000 : ℝ)^1657 := by
    have hnat : (966425317 : ℕ)^2169*2500000000000^1657 ≤ 290789804707^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966425317 5000000000 290789804707 2500000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410216779/10000000000 : ℝ)^2169 ≤ (44748665897201/100000000000000 : ℝ)^1657 := by
    have hnat : (5410216779 : ℕ)^2169*100000000000000^1657 ≤ 44748665897201^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410216779 10000000000 44748665897201 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305632343/10000000000 : ℝ), (-966425317/5000000000 : ℝ), (5410216779/10000000000 : ℝ)] ![(21809870951059/50000000000000 : ℝ), (290789804707/2500000000000 : ℝ), (44748665897201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305632343/10000000000 : ℝ)|^2169 ≤ (21809870951059/50000000000000 : ℝ)^1657
        have hw : |(5305632343/10000000000 : ℝ)|=(5305632343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-966425317/5000000000 : ℝ)|^2169 ≤ (290789804707/2500000000000 : ℝ)^1657
        have hw : |(-966425317/5000000000 : ℝ)|=(966425317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410216779/10000000000 : ℝ)|^2169 ≤ (44748665897201/100000000000000 : ℝ)^1657
        have hw : |(5410216779/10000000000 : ℝ)|=(5410216779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s7_6 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305632889/10000000000 : ℝ)*x 0 + (338138529/625000000 : ℝ)*x 1 + (-1932850321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305632889/10000000000 : ℝ)^2169 ≤ (8723949555607/20000000000000 : ℝ)^1657 := by
    have hnat : (5305632889 : ℕ)^2169*20000000000000^1657 ≤ 8723949555607^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305632889 10000000000 8723949555607 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338138529/625000000 : ℝ)^2169 ≤ (2237433124337/5000000000000 : ℝ)^1657 := by
    have hnat : (338138529 : ℕ)^2169*5000000000000^1657 ≤ 2237433124337^1657*625000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338138529 625000000 2237433124337 5000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1932850321/10000000000 : ℝ)^2169 ≤ (11631589722683/100000000000000 : ℝ)^1657 := by
    have hnat : (1932850321 : ℕ)^2169*100000000000000^1657 ≤ 11631589722683^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932850321 10000000000 11631589722683 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305632889/10000000000 : ℝ), (338138529/625000000 : ℝ), (-1932850321/10000000000 : ℝ)] ![(8723949555607/20000000000000 : ℝ), (2237433124337/5000000000000 : ℝ), (11631589722683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305632889/10000000000 : ℝ)|^2169 ≤ (8723949555607/20000000000000 : ℝ)^1657
        have hw : |(5305632889/10000000000 : ℝ)|=(5305632889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338138529/625000000 : ℝ)|^2169 ≤ (2237433124337/5000000000000 : ℝ)^1657
        have hw : |(338138529/625000000 : ℝ)|=(338138529/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1932850321/10000000000 : ℝ)|^2169 ≤ (11631589722683/100000000000000 : ℝ)^1657
        have hw : |(-1932850321/10000000000 : ℝ)|=(1932850321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s7_7 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1079330131/2500000000 : ℝ)*x 0 + (561824067/1250000000 : ℝ)*x 1 + (1036637773/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079330131/2500000000 : ℝ)^2169 ≤ (33304151294331/100000000000000 : ℝ)^1657 := by
    have hnat : (1079330131 : ℕ)^2169*100000000000000^1657 ≤ 33304151294331^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079330131 2500000000 33304151294331 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561824067/1250000000 : ℝ)^2169 ≤ (35105435243569/100000000000000 : ℝ)^1657 := by
    have hnat : (561824067 : ℕ)^2169*100000000000000^1657 ≤ 35105435243569^1657*1250000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561824067 1250000000 35105435243569 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036637773/2500000000 : ℝ)^2169 ≤ (15795206722529/50000000000000 : ℝ)^1657 := by
    have hnat : (1036637773 : ℕ)^2169*50000000000000^1657 ≤ 15795206722529^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036637773 2500000000 15795206722529 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079330131/2500000000 : ℝ), (561824067/1250000000 : ℝ), (1036637773/2500000000 : ℝ)] ![(33304151294331/100000000000000 : ℝ), (35105435243569/100000000000000 : ℝ), (15795206722529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079330131/2500000000 : ℝ)|^2169 ≤ (33304151294331/100000000000000 : ℝ)^1657
        have hw : |(1079330131/2500000000 : ℝ)|=(1079330131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561824067/1250000000 : ℝ)|^2169 ≤ (35105435243569/100000000000000 : ℝ)^1657
        have hw : |(561824067/1250000000 : ℝ)|=(561824067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036637773/2500000000 : ℝ)|^2169 ≤ (15795206722529/50000000000000 : ℝ)^1657
        have hw : |(1036637773/2500000000 : ℝ)|=(1036637773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1378_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (351/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1841/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14729/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14729/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14729/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14729/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14729/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14729/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11231/100000 : ℝ) ^ (4337/1024 : ℝ) ≤ (4755084144117689/50000000000000000000 : ℝ) := by
    have hpowers : (11231/100000 : ℝ)^4337 ≤ (4755084144117689/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11231 : ℕ)^4337*50000000000000000000^1024 ≤ 4755084144117689^1024*100000^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11231 100000 4755084144117689 50000000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11231/100000 : ℝ)) (X := (4755084144117689/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14729/100000 : ℝ) ^ (4337/1024 : ℝ) ≤ (7496548151435699/25000000000000000000 : ℝ) := by
    have hpowers : (14729/100000 : ℝ)^4337 ≤ (7496548151435699/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14729 : ℕ)^4337*25000000000000000000^1024 ≤ 7496548151435699^1024*100000^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14729 100000 7496548151435699 25000000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14729/100000 : ℝ)) (X := (7496548151435699/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004755084144117689/25000000000000000000 : ℝ) ≤ (10000449052567937/10000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (25004755084144117689/25000000000000000000 : ℝ)^1024 ≤ (10000449052567937/10000000000000000 : ℝ)^4337 := by
      have hnat : (25004755084144117689 : ℕ)^1024*10000000000000000^4337 ≤ 10000449052567937^4337*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004755084144117689 25000000000000000000 10000449052567937 10000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000449052567937/10000000000000000 : ℝ)) (X := (25004755084144117689/25000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019748180446989087/50000000000000000000 : ℝ) ≤ (10000932399671653/10000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (50019748180446989087/50000000000000000000 : ℝ)^1024 ≤ (10000932399671653/10000000000000000 : ℝ)^4337 := by
      have hnat : (50019748180446989087 : ℕ)^1024*10000000000000000^4337 ≤ 10000932399671653^4337*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019748180446989087 50000000000000000000 10000932399671653 10000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000932399671653/10000000000000000 : ℝ)) (X := (50019748180446989087/50000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507496548151435699/12500000000000000000 : ℝ) ≤ (10001415746775369/10000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (12507496548151435699/12500000000000000000 : ℝ)^1024 ≤ (10001415746775369/10000000000000000 : ℝ)^4337 := by
      have hnat : (12507496548151435699 : ℕ)^1024*10000000000000000^4337 ≤ 10001415746775369^4337*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507496548151435699 12500000000000000000 10001415746775369 10000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001415746775369/10000000000000000 : ℝ)) (X := (12507496548151435699/12500000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4755084144117689/50000000000000000000 : ℝ) ≤ ((1589577901965407947/1590000000000000000 : ℝ)+2*(120836775929/87450000000000 : ℝ)*(11231/100000 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (1589577901965407947/1590000000000000000 : ℝ)+2*(120836775929/87450000000000 : ℝ)*(11231/100000 : ℝ)=(10000449052567937/10000000000000000 : ℝ) by norm_num, show 1+2*(4755084144117689/50000000000000000000 : ℝ)=(25004755084144117689/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7496548151435699/25000000000000000000 : ℝ)+(4755084144117689/50000000000000000000 : ℝ) ≤ ((1589577901965407947/1590000000000000000 : ℝ)+(120836775929/87450000000000 : ℝ)*((14729/100000 : ℝ)+(11231/100000 : ℝ)))^(4337/1024 : ℝ) := by
    rw [show (1589577901965407947/1590000000000000000 : ℝ)+(120836775929/87450000000000 : ℝ)*((14729/100000 : ℝ)+(11231/100000 : ℝ))=(10000932399671653/10000000000000000 : ℝ) by norm_num, show 1+(7496548151435699/25000000000000000000 : ℝ)+(4755084144117689/50000000000000000000 : ℝ)=(50019748180446989087/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7496548151435699/25000000000000000000 : ℝ) ≤ ((1589577901965407947/1590000000000000000 : ℝ)+2*(120836775929/87450000000000 : ℝ)*(14729/100000 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (1589577901965407947/1590000000000000000 : ℝ)+2*(120836775929/87450000000000 : ℝ)*(14729/100000 : ℝ)=(10001415746775369/10000000000000000 : ℝ) by norm_num, show 1+2*(7496548151435699/25000000000000000000 : ℝ)=(12507496548151435699/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1589577901965407947/1590000000000000000 : ℝ)*(X 1 0+X 2 0)+(120836775929/87450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (1589577901965407947/1590000000000000000 : ℝ)) (alpha := (120836775929/87450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1589577901965407947/1590000000000000000 : ℝ)*(X 0 1+X 2 1)+(120836775929/87450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (1589577901965407947/1590000000000000000 : ℝ)) (alpha := (120836775929/87450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1589577901965407947/1590000000000000000 : ℝ)*(X 0 2+X 1 2)+(120836775929/87450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (1589577901965407947/1590000000000000000 : ℝ)) (alpha := (120836775929/87450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1006638963/5000000000 : ℝ)*X 0 0+(2705405439/5000000000 : ℝ)*X 0 1+(5245684233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674168473/5000000000 : ℝ)*X 1 0+(-524345781/2500000000 : ℝ)*X 1 1+(655710517/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348337021/10000000000 : ℝ)*X 2 0+(1311420833/2500000000 : ℝ)*X 2 1+(-2097384091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158648533/5000000000 : ℝ)*X 0 0+(4145284861/10000000000 : ℝ)*X 0 1+(2247925339/5000000000 : ℝ)*X 0 2+(2158648533/5000000000 : ℝ)*X 1 0+(4145284861/10000000000 : ℝ)*X 1 1+(2247925339/5000000000 : ℝ)*X 1 2+(2158648533/5000000000 : ℝ)*X 2 0+(4145284861/10000000000 : ℝ)*X 2 1+(2247925339/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1006644651/5000000000 : ℝ)*X 0 0+(1049255247/2000000000 : ℝ)*X 0 1+(5410216117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305632343/10000000000 : ℝ)*X 1 0+(-966425317/5000000000 : ℝ)*X 1 1+(5410216779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305632889/10000000000 : ℝ)*X 2 0+(338138529/625000000 : ℝ)*X 2 1+(-1932850321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079330131/2500000000 : ℝ)*X 0 0+(561824067/1250000000 : ℝ)*X 0 1+(1036637773/2500000000 : ℝ)*X 0 2+(1079330131/2500000000 : ℝ)*X 1 0+(561824067/1250000000 : ℝ)*X 1 1+(1036637773/2500000000 : ℝ)*X 1 2+(1079330131/2500000000 : ℝ)*X 2 0+(561824067/1250000000 : ℝ)*X 2 1+(1036637773/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12570136452376473314511631/2650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1016992609/100000000000000 : ℝ)*(base19) + (213694619/20000000000000 : ℝ)*(base23) + (212383799/50000000000000 : ℝ)*(upper3) + (124457187/100000000000000 : ℝ)*(lower4) + (7473403/1562500000000 : ℝ)*(upper5) + (445426913485427/10000000000000 : ℝ)*(major0) + (445426913485427/10000000000000 : ℝ)*(major1) + (445426913485427/10000000000000 : ℝ)*(major2) + (6055959804401967/100000000000000 : ℝ)*(sp0) + (6055958787409359/100000000000000 : ℝ)*(sp1) + (6055925403469033/100000000000000 : ℝ)*(sp2) + (570511182328667/20000000000000 : ℝ)*(sp3) + (33332459839/100000000000000 : ℝ)*(sp6) + (1399721769/6250000000000 : ℝ)*(sp7) + (2852578307191639/100000000000000 : ℝ)*(f.failure) + (6055959804401967/100000000000000 : ℝ)*(f.sum) + (349665160981/109312500000000000000000000 : ℝ)*base65 + (236120902947157353/58300000000000000000000000000000 : ℝ)*base67 + (89540448686042647/58300000000000000000000000000000 : ℝ)*base70 + (1888021284292657353/58300000000000000000000000000000 : ℝ)*base71 + (1333934462131/349800000000000000000000000 : ℝ)*base74 + (1183140157193942647/58300000000000000000000000000000 : ℝ)*base76 + (738045741807657353/58300000000000000000000000000000 : ℝ)*base77 + (82520794771357353/58300000000000000000000000000000 : ℝ)*base79 + (2691070136123/437250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5201201/5000000000000000000000 : ℝ)*base90 + (5201201/5000000000000000000000 : ℝ)*base92 + (5201201/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61885376704400773690786629/13250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180552281/100000000000000 : ℝ)*(base23) + (5426747/2500000000000 : ℝ)*(lower1) + (6355159/6250000000000 : ℝ)*(lower2) + (46684031/25000000000000 : ℝ)*(upper3) + (176210491/100000000000000 : ℝ)*(upper4) + (2243252999842331/50000000000000 : ℝ)*(major0) + (2243252999842331/50000000000000 : ℝ)*(major1) + (2243252999842331/50000000000000 : ℝ)*(major2) + (594775433/6250000000000 : ℝ)*(sp2) + (54915883/10000000000000 : ℝ)*(sp3) + (6099788582510421/100000000000000 : ℝ)*(sp4) + (6099788582510421/100000000000000 : ℝ)*(sp5) + (1524944721387803/25000000000000 : ℝ)*(sp6) + (1436611356006791/50000000000000 : ℝ)*(sp7) + (718305815293103/25000000000000 : ℝ)*(f.failure) + (6099788582510421/100000000000000 : ℝ)*(f.sum) + (12227308591237/4372500000000000000000000000 : ℝ)*base66 + (1096283893840583009/291500000000000000000000000000000 : ℝ)*base67 + (2251605658844583009/291500000000000000000000000000000 : ℝ)*base69 + (2101301668029583009/291500000000000000000000000000000 : ℝ)*base71 + (2368492961833/1093125000000000000000000000 : ℝ)*base74 + (1778822187211583009/291500000000000000000000000000000 : ℝ)*base75 + (4021660947830083009/291500000000000000000000000000000 : ℝ)*base77 + (3053900670137083009/291500000000000000000000000000000 : ℝ)*base79 + (10357303668521/2186250000000000000000000000 : ℝ)*base82 + (7119577/1250000000000000000000 : ℝ)*base90 + (7119577/1250000000000000000000 : ℝ)*base92 + (7119577/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1378_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1378_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1378_box_0 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-92441559/500000000 : ℝ)*x 0 + (2694212769/5000000000 : ℝ)*x 1 + (5388425589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92441559/500000000 : ℝ)^2169 ≤ (10974235122237/100000000000000 : ℝ)^1657 := by
    have hnat : (92441559 : ℕ)^2169*100000000000000^1657 ≤ 10974235122237^1657*500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92441559 500000000 10974235122237 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694212769/5000000000 : ℝ)^2169 ≤ (44512882161091/100000000000000 : ℝ)^1657 := by
    have hnat : (2694212769 : ℕ)^2169*100000000000000^1657 ≤ 44512882161091^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694212769 5000000000 44512882161091 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388425589/10000000000 : ℝ)^2169 ≤ (44512882712573/100000000000000 : ℝ)^1657 := by
    have hnat : (5388425589 : ℕ)^2169*100000000000000^1657 ≤ 44512882712573^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388425589 10000000000 44512882712573 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-92441559/500000000 : ℝ), (2694212769/5000000000 : ℝ), (5388425589/10000000000 : ℝ)] ![(10974235122237/100000000000000 : ℝ), (44512882161091/100000000000000 : ℝ), (44512882712573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-92441559/500000000 : ℝ)|^2169 ≤ (10974235122237/100000000000000 : ℝ)^1657
        have hw : |(-92441559/500000000 : ℝ)|=(92441559/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694212769/5000000000 : ℝ)|^2169 ≤ (44512882161091/100000000000000 : ℝ)^1657
        have hw : |(2694212769/5000000000 : ℝ)|=(2694212769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388425589/10000000000 : ℝ)|^2169 ≤ (44512882712573/100000000000000 : ℝ)^1657
        have hw : |(5388425589/10000000000 : ℝ)|=(5388425589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_1 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2642803927/5000000000 : ℝ)*x 0 + (-397973079/2000000000 : ℝ)*x 1 + (673553199/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642803927/5000000000 : ℝ)^2169 ≤ (43404369082129/100000000000000 : ℝ)^1657 := by
    have hnat : (2642803927 : ℕ)^2169*100000000000000^1657 ≤ 43404369082129^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642803927 5000000000 43404369082129 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397973079/2000000000 : ℝ)^2169 ≤ (12082748160911/100000000000000 : ℝ)^1657 := by
    have hnat : (397973079 : ℕ)^2169*100000000000000^1657 ≤ 12082748160911^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397973079 2000000000 12082748160911 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673553199/1250000000 : ℝ)^2169 ≤ (44512882745013/100000000000000 : ℝ)^1657 := by
    have hnat : (673553199 : ℕ)^2169*100000000000000^1657 ≤ 44512882745013^1657*1250000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673553199 1250000000 44512882745013 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642803927/5000000000 : ℝ), (-397973079/2000000000 : ℝ), (673553199/1250000000 : ℝ)] ![(43404369082129/100000000000000 : ℝ), (12082748160911/100000000000000 : ℝ), (44512882745013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642803927/5000000000 : ℝ)|^2169 ≤ (43404369082129/100000000000000 : ℝ)^1657
        have hw : |(2642803927/5000000000 : ℝ)|=(2642803927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397973079/2000000000 : ℝ)|^2169 ≤ (12082748160911/100000000000000 : ℝ)^1657
        have hw : |(-397973079/2000000000 : ℝ)|=(397973079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673553199/1250000000 : ℝ)|^2169 ≤ (44512882745013/100000000000000 : ℝ)^1657
        have hw : |(673553199/1250000000 : ℝ)|=(673553199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_2 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1321401939/2500000000 : ℝ)*x 0 + (5388425691/10000000000 : ℝ)*x 1 + (-1989865393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321401939/2500000000 : ℝ)^2169 ≤ (43404368028709/100000000000000 : ℝ)^1657 := by
    have hnat : (1321401939 : ℕ)^2169*100000000000000^1657 ≤ 43404368028709^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321401939 2500000000 43404368028709 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388425691/10000000000 : ℝ)^2169 ≤ (2782055238471/6250000000000 : ℝ)^1657 := by
    have hnat : (5388425691 : ℕ)^2169*6250000000000^1657 ≤ 2782055238471^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388425691 10000000000 2782055238471 6250000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1989865393/10000000000 : ℝ)^2169 ≤ (2416549629003/20000000000000 : ℝ)^1657 := by
    have hnat : (1989865393 : ℕ)^2169*20000000000000^1657 ≤ 2416549629003^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989865393 10000000000 2416549629003 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321401939/2500000000 : ℝ), (5388425691/10000000000 : ℝ), (-1989865393/10000000000 : ℝ)] ![(43404368028709/100000000000000 : ℝ), (2782055238471/6250000000000 : ℝ), (2416549629003/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321401939/2500000000 : ℝ)|^2169 ≤ (43404368028709/100000000000000 : ℝ)^1657
        have hw : |(1321401939/2500000000 : ℝ)|=(1321401939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388425691/10000000000 : ℝ)|^2169 ≤ (2782055238471/6250000000000 : ℝ)^1657
        have hw : |(5388425691/10000000000 : ℝ)|=(5388425691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1989865393/10000000000 : ℝ)|^2169 ≤ (2416549629003/20000000000000 : ℝ)^1657
        have hw : |(-1989865393/10000000000 : ℝ)|=(1989865393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_3 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2232330887/5000000000 : ℝ)*x 0 + (4247423849/10000000000 : ℝ)*x 1 + (2123712027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2232330887/5000000000 : ℝ)^2169 ≤ (434996728559/1250000000000 : ℝ)^1657 := by
    have hnat : (2232330887 : ℕ)^2169*1250000000000^1657 ≤ 434996728559^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232330887 5000000000 434996728559 1250000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247423849/10000000000 : ℝ)^2169 ≤ (6520025965013/20000000000000 : ℝ)^1657 := by
    have hnat : (4247423849 : ℕ)^2169*20000000000000^1657 ≤ 6520025965013^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247423849 10000000000 6520025965013 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123712027/5000000000 : ℝ)^2169 ≤ (32600131884673/100000000000000 : ℝ)^1657 := by
    have hnat : (2123712027 : ℕ)^2169*100000000000000^1657 ≤ 32600131884673^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123712027 5000000000 32600131884673 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2232330887/5000000000 : ℝ), (4247423849/10000000000 : ℝ), (2123712027/5000000000 : ℝ)] ![(434996728559/1250000000000 : ℝ), (6520025965013/20000000000000 : ℝ), (32600131884673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2232330887/5000000000 : ℝ)|^2169 ≤ (434996728559/1250000000000 : ℝ)^1657
        have hw : |(2232330887/5000000000 : ℝ)|=(2232330887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4247423849/10000000000 : ℝ)|^2169 ≤ (6520025965013/20000000000000 : ℝ)^1657
        have hw : |(4247423849/10000000000 : ℝ)|=(4247423849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123712027/5000000000 : ℝ)|^2169 ≤ (32600131884673/100000000000000 : ℝ)^1657
        have hw : |(2123712027/5000000000 : ℝ)|=(2123712027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_4 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2180468167/10000000000 : ℝ)*x 0 + (164552137/312500000 : ℝ)*x 1 + (1316417113/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180468167/10000000000 : ℝ)^2169 ≤ (13619677156759/100000000000000 : ℝ)^1657 := by
    have hnat : (2180468167 : ℕ)^2169*100000000000000^1657 ≤ 13619677156759^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180468167 10000000000 13619677156759 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164552137/312500000 : ℝ)^2169 ≤ (2699385065611/6250000000000 : ℝ)^1657 := by
    have hnat : (164552137 : ℕ)^2169*6250000000000^1657 ≤ 2699385065611^1657*312500000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164552137 312500000 2699385065611 6250000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316417113/2500000000 : ℝ)^2169 ≤ (10797540444967/25000000000000 : ℝ)^1657 := by
    have hnat : (1316417113 : ℕ)^2169*25000000000000^1657 ≤ 10797540444967^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316417113 2500000000 10797540444967 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2180468167/10000000000 : ℝ), (164552137/312500000 : ℝ), (1316417113/2500000000 : ℝ)] ![(13619677156759/100000000000000 : ℝ), (2699385065611/6250000000000 : ℝ), (10797540444967/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2180468167/10000000000 : ℝ)|^2169 ≤ (13619677156759/100000000000000 : ℝ)^1657
        have hw : |(-2180468167/10000000000 : ℝ)|=(2180468167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164552137/312500000 : ℝ)|^2169 ≤ (2699385065611/6250000000000 : ℝ)^1657
        have hw : |(164552137/312500000 : ℝ)|=(164552137/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316417113/2500000000 : ℝ)|^2169 ≤ (10797540444967/25000000000000 : ℝ)^1657
        have hw : |(1316417113/2500000000 : ℝ)|=(1316417113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_5 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (335731227/625000000 : ℝ)*x 0 + (-2039369521/10000000000 : ℝ)*x 1 + (658208587/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335731227/625000000 : ℝ)^2169 ≤ (44332105627563/100000000000000 : ℝ)^1657 := by
    have hnat : (335731227 : ℕ)^2169*100000000000000^1657 ≤ 44332105627563^1657*625000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335731227 625000000 44332105627563 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2039369521/10000000000 : ℝ)^2169 ≤ (12477729955067/100000000000000 : ℝ)^1657 := by
    have hnat : (2039369521 : ℕ)^2169*100000000000000^1657 ≤ 12477729955067^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039369521 10000000000 12477729955067 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658208587/1250000000 : ℝ)^2169 ≤ (5398770549951/12500000000000 : ℝ)^1657 := by
    have hnat : (658208587 : ℕ)^2169*12500000000000^1657 ≤ 5398770549951^1657*1250000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658208587 1250000000 5398770549951 12500000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335731227/625000000 : ℝ), (-2039369521/10000000000 : ℝ), (658208587/1250000000 : ℝ)] ![(44332105627563/100000000000000 : ℝ), (12477729955067/100000000000000 : ℝ), (5398770549951/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335731227/625000000 : ℝ)|^2169 ≤ (44332105627563/100000000000000 : ℝ)^1657
        have hw : |(335731227/625000000 : ℝ)|=(335731227/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2039369521/10000000000 : ℝ)|^2169 ≤ (12477729955067/100000000000000 : ℝ)^1657
        have hw : |(-2039369521/10000000000 : ℝ)|=(2039369521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658208587/1250000000 : ℝ)|^2169 ≤ (5398770549951/12500000000000 : ℝ)^1657
        have hw : |(658208587/1250000000 : ℝ)|=(658208587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_6 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2685850051/5000000000 : ℝ)*x 0 + (2632834107/5000000000 : ℝ)*x 1 + (-407873907/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685850051/5000000000 : ℝ)^2169 ≤ (8866422140993/20000000000000 : ℝ)^1657 := by
    have hnat : (2685850051 : ℕ)^2169*20000000000000^1657 ≤ 8866422140993^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685850051 5000000000 8866422140993 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632834107/5000000000 : ℝ)^2169 ≤ (10797539806137/25000000000000 : ℝ)^1657 := by
    have hnat : (2632834107 : ℕ)^2169*25000000000000^1657 ≤ 10797539806137^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632834107 5000000000 10797539806137 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407873907/2000000000 : ℝ)^2169 ≤ (12477730067193/100000000000000 : ℝ)^1657 := by
    have hnat : (407873907 : ℕ)^2169*100000000000000^1657 ≤ 12477730067193^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407873907 2000000000 12477730067193 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685850051/5000000000 : ℝ), (2632834107/5000000000 : ℝ), (-407873907/2000000000 : ℝ)] ![(8866422140993/20000000000000 : ℝ), (10797539806137/25000000000000 : ℝ), (12477730067193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685850051/5000000000 : ℝ)|^2169 ≤ (8866422140993/20000000000000 : ℝ)^1657
        have hw : |(2685850051/5000000000 : ℝ)|=(2685850051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632834107/5000000000 : ℝ)|^2169 ≤ (10797539806137/25000000000000 : ℝ)^1657
        have hw : |(2632834107/5000000000 : ℝ)|=(2632834107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407873907/2000000000 : ℝ)|^2169 ≤ (12477730067193/100000000000000 : ℝ)^1657
        have hw : |(-407873907/2000000000 : ℝ)|=(407873907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_7 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4168951873/10000000000 : ℝ)*x 0 + (2197613211/5000000000 : ℝ)*x 1 + (219761327/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4168951873/10000000000 : ℝ)^2169 ≤ (31813992114249/100000000000000 : ℝ)^1657 := by
    have hnat : (4168951873 : ℕ)^2169*100000000000000^1657 ≤ 31813992114249^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168951873 10000000000 31813992114249 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197613211/5000000000 : ℝ)^2169 ≤ (4261625417027/12500000000000 : ℝ)^1657 := by
    have hnat : (2197613211 : ℕ)^2169*12500000000000^1657 ≤ 4261625417027^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197613211 5000000000 4261625417027 12500000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219761327/500000000 : ℝ)^2169 ≤ (4261625566793/12500000000000 : ℝ)^1657 := by
    have hnat : (219761327 : ℕ)^2169*12500000000000^1657 ≤ 4261625566793^1657*500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219761327 500000000 4261625566793 12500000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4168951873/10000000000 : ℝ), (2197613211/5000000000 : ℝ), (219761327/500000000 : ℝ)] ![(31813992114249/100000000000000 : ℝ), (4261625417027/12500000000000 : ℝ), (4261625566793/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4168951873/10000000000 : ℝ)|^2169 ≤ (31813992114249/100000000000000 : ℝ)^1657
        have hw : |(4168951873/10000000000 : ℝ)|=(4168951873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2197613211/5000000000 : ℝ)|^2169 ≤ (4261625417027/12500000000000 : ℝ)^1657
        have hw : |(2197613211/5000000000 : ℝ)|=(2197613211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219761327/500000000 : ℝ)|^2169 ≤ (4261625566793/12500000000000 : ℝ)^1657
        have hw : |(219761327/500000000 : ℝ)|=(219761327/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_8 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2110734563/10000000000 : ℝ)*x 0 + (5180992037/10000000000 : ℝ)*x 1 + (5402427867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110734563/10000000000 : ℝ)^2169 ≤ (13052356012747/100000000000000 : ℝ)^1657 := by
    have hnat : (2110734563 : ℕ)^2169*100000000000000^1657 ≤ 13052356012747^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110734563 10000000000 13052356012747 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180992037/10000000000 : ℝ)^2169 ≤ (42283288770249/100000000000000 : ℝ)^1657 := by
    have hnat : (5180992037 : ℕ)^2169*100000000000000^1657 ≤ 42283288770249^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180992037 10000000000 42283288770249 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402427867/10000000000 : ℝ)^2169 ≤ (22332177605303/50000000000000 : ℝ)^1657 := by
    have hnat : (5402427867 : ℕ)^2169*50000000000000^1657 ≤ 22332177605303^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402427867 10000000000 22332177605303 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2110734563/10000000000 : ℝ), (5180992037/10000000000 : ℝ), (5402427867/10000000000 : ℝ)] ![(13052356012747/100000000000000 : ℝ), (42283288770249/100000000000000 : ℝ), (22332177605303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2110734563/10000000000 : ℝ)|^2169 ≤ (13052356012747/100000000000000 : ℝ)^1657
        have hw : |(-2110734563/10000000000 : ℝ)|=(2110734563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180992037/10000000000 : ℝ)|^2169 ≤ (42283288770249/100000000000000 : ℝ)^1657
        have hw : |(5180992037/10000000000 : ℝ)|=(5180992037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402427867/10000000000 : ℝ)|^2169 ≤ (22332177605303/50000000000000 : ℝ)^1657
        have hw : |(5402427867/10000000000 : ℝ)|=(5402427867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_9 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (527578303/1000000000 : ℝ)*x 0 + (-396817791/2000000000 : ℝ)*x 1 + (5402427759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527578303/1000000000 : ℝ)^2169 ≤ (43298790569021/100000000000000 : ℝ)^1657 := by
    have hnat : (527578303 : ℕ)^2169*100000000000000^1657 ≤ 43298790569021^1657*1000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527578303 1000000000 43298790569021 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (396817791/2000000000 : ℝ)^2169 ≤ (1504606922393/12500000000000 : ℝ)^1657 := by
    have hnat : (396817791 : ℕ)^2169*12500000000000^1657 ≤ 1504606922393^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396817791 2000000000 1504606922393 12500000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402427759/10000000000 : ℝ)^2169 ≤ (1786574161673/4000000000000 : ℝ)^1657 := by
    have hnat : (5402427759 : ℕ)^2169*4000000000000^1657 ≤ 1786574161673^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402427759 10000000000 1786574161673 4000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527578303/1000000000 : ℝ), (-396817791/2000000000 : ℝ), (5402427759/10000000000 : ℝ)] ![(43298790569021/100000000000000 : ℝ), (1504606922393/12500000000000 : ℝ), (1786574161673/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527578303/1000000000 : ℝ)|^2169 ≤ (43298790569021/100000000000000 : ℝ)^1657
        have hw : |(527578303/1000000000 : ℝ)|=(527578303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-396817791/2000000000 : ℝ)|^2169 ≤ (1504606922393/12500000000000 : ℝ)^1657
        have hw : |(-396817791/2000000000 : ℝ)|=(396817791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402427759/10000000000 : ℝ)|^2169 ≤ (1786574161673/4000000000000 : ℝ)^1657
        have hw : |(5402427759/10000000000 : ℝ)|=(5402427759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_10 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (263789131/500000000 : ℝ)*x 0 + (5402427913/10000000000 : ℝ)*x 1 + (-19840893/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263789131/500000000 : ℝ)^2169 ≤ (10824696541097/25000000000000 : ℝ)^1657 := by
    have hnat : (263789131 : ℕ)^2169*25000000000000^1657 ≤ 10824696541097^1657*500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263789131 500000000 10824696541097 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402427913/10000000000 : ℝ)^2169 ≤ (44664355708419/100000000000000 : ℝ)^1657 := by
    have hnat : (5402427913 : ℕ)^2169*100000000000000^1657 ≤ 44664355708419^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402427913 10000000000 44664355708419 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19840893/100000000 : ℝ)^2169 ≤ (3009214529719/25000000000000 : ℝ)^1657 := by
    have hnat : (19840893 : ℕ)^2169*25000000000000^1657 ≤ 3009214529719^1657*100000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19840893 100000000 3009214529719 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263789131/500000000 : ℝ), (5402427913/10000000000 : ℝ), (-19840893/100000000 : ℝ)] ![(10824696541097/25000000000000 : ℝ), (44664355708419/100000000000000 : ℝ), (3009214529719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263789131/500000000 : ℝ)|^2169 ≤ (10824696541097/25000000000000 : ℝ)^1657
        have hw : |(263789131/500000000 : ℝ)|=(263789131/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402427913/10000000000 : ℝ)|^2169 ≤ (44664355708419/100000000000000 : ℝ)^1657
        have hw : |(5402427913/10000000000 : ℝ)|=(5402427913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19840893/100000000 : ℝ)|^2169 ≤ (3009214529719/25000000000000 : ℝ)^1657
        have hw : |(-19840893/100000000 : ℝ)|=(19840893/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_11 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (449783439/1000000000 : ℝ)*x 0 + (1057637409/2500000000 : ℝ)*x 1 + (4230551071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449783439/1000000000 : ℝ)^2169 ≤ (35138583669921/100000000000000 : ℝ)^1657 := by
    have hnat : (449783439 : ℕ)^2169*100000000000000^1657 ≤ 35138583669921^1657*1000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449783439 1000000000 35138583669921 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057637409/2500000000 : ℝ)^2169 ≤ (16215350478471/50000000000000 : ℝ)^1657 := by
    have hnat : (1057637409 : ℕ)^2169*50000000000000^1657 ≤ 16215350478471^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057637409 2500000000 16215350478471 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230551071/10000000000 : ℝ)^2169 ≤ (16215357678239/50000000000000 : ℝ)^1657 := by
    have hnat : (4230551071 : ℕ)^2169*50000000000000^1657 ≤ 16215357678239^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230551071 10000000000 16215357678239 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(449783439/1000000000 : ℝ), (1057637409/2500000000 : ℝ), (4230551071/10000000000 : ℝ)] ![(35138583669921/100000000000000 : ℝ), (16215350478471/50000000000000 : ℝ), (16215357678239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(449783439/1000000000 : ℝ)|^2169 ≤ (35138583669921/100000000000000 : ℝ)^1657
        have hw : |(449783439/1000000000 : ℝ)|=(449783439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057637409/2500000000 : ℝ)|^2169 ≤ (16215350478471/50000000000000 : ℝ)^1657
        have hw : |(1057637409/2500000000 : ℝ)|=(1057637409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230551071/10000000000 : ℝ)|^2169 ≤ (16215357678239/50000000000000 : ℝ)^1657
        have hw : |(4230551071/10000000000 : ℝ)|=(4230551071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_12 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-119927167/625000000 : ℝ)*x 0 + (5470975279/10000000000 : ℝ)*x 1 + (1050914437/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (119927167/625000000 : ℝ)^2169 ≤ (5760654007701/50000000000000 : ℝ)^1657 := by
    have hnat : (119927167 : ℕ)^2169*50000000000000^1657 ≤ 5760654007701^1657*625000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119927167 625000000 5760654007701 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470975279/10000000000 : ℝ)^2169 ≤ (45407628004177/100000000000000 : ℝ)^1657 := by
    have hnat : (5470975279 : ℕ)^2169*100000000000000^1657 ≤ 45407628004177^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470975279 10000000000 45407628004177 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050914437/2000000000 : ℝ)^2169 ≤ (21535531984591/50000000000000 : ℝ)^1657 := by
    have hnat : (1050914437 : ℕ)^2169*50000000000000^1657 ≤ 21535531984591^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050914437 2000000000 21535531984591 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-119927167/625000000 : ℝ), (5470975279/10000000000 : ℝ), (1050914437/2000000000 : ℝ)] ![(5760654007701/50000000000000 : ℝ), (45407628004177/100000000000000 : ℝ), (21535531984591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-119927167/625000000 : ℝ)|^2169 ≤ (5760654007701/50000000000000 : ℝ)^1657
        have hw : |(-119927167/625000000 : ℝ)|=(119927167/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470975279/10000000000 : ℝ)|^2169 ≤ (45407628004177/100000000000000 : ℝ)^1657
        have hw : |(5470975279/10000000000 : ℝ)|=(5470975279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050914437/2000000000 : ℝ)|^2169 ≤ (21535531984591/50000000000000 : ℝ)^1657
        have hw : |(1050914437/2000000000 : ℝ)|=(1050914437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_13 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1344869923/2500000000 : ℝ)*x 0 + (-2043742087/10000000000 : ℝ)*x 1 + (5254572411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344869923/2500000000 : ℝ)^2169 ≤ (44416172282079/100000000000000 : ℝ)^1657 := by
    have hnat : (1344869923 : ℕ)^2169*100000000000000^1657 ≤ 44416172282079^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344869923 2500000000 44416172282079 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2043742087/10000000000 : ℝ)^2169 ≤ (3128190325601/25000000000000 : ℝ)^1657 := by
    have hnat : (2043742087 : ℕ)^2169*25000000000000^1657 ≤ 3128190325601^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043742087 10000000000 3128190325601 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254572411/10000000000 : ℝ)^2169 ≤ (21535533197041/50000000000000 : ℝ)^1657 := by
    have hnat : (5254572411 : ℕ)^2169*50000000000000^1657 ≤ 21535533197041^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254572411 10000000000 21535533197041 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344869923/2500000000 : ℝ), (-2043742087/10000000000 : ℝ), (5254572411/10000000000 : ℝ)] ![(44416172282079/100000000000000 : ℝ), (3128190325601/25000000000000 : ℝ), (21535533197041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344869923/2500000000 : ℝ)|^2169 ≤ (44416172282079/100000000000000 : ℝ)^1657
        have hw : |(1344869923/2500000000 : ℝ)|=(1344869923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2043742087/10000000000 : ℝ)|^2169 ≤ (3128190325601/25000000000000 : ℝ)^1657
        have hw : |(-2043742087/10000000000 : ℝ)|=(2043742087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254572411/10000000000 : ℝ)|^2169 ≤ (21535533197041/50000000000000 : ℝ)^1657
        have hw : |(5254572411/10000000000 : ℝ)|=(5254572411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_14 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5379479699/10000000000 : ℝ)*x 0 + (328410771/625000000 : ℝ)*x 1 + (-1021871089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379479699/10000000000 : ℝ)^2169 ≤ (22208086178867/50000000000000 : ℝ)^1657 := by
    have hnat : (5379479699 : ℕ)^2169*50000000000000^1657 ≤ 22208086178867^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379479699 10000000000 22208086178867 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328410771/625000000 : ℝ)^2169 ≤ (21535532794679/50000000000000 : ℝ)^1657 := by
    have hnat : (328410771 : ℕ)^2169*50000000000000^1657 ≤ 21535532794679^1657*625000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328410771 625000000 21535532794679 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021871089/5000000000 : ℝ)^2169 ≤ (12512762031703/100000000000000 : ℝ)^1657 := by
    have hnat : (1021871089 : ℕ)^2169*100000000000000^1657 ≤ 12512762031703^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021871089 5000000000 12512762031703 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379479699/10000000000 : ℝ), (328410771/625000000 : ℝ), (-1021871089/5000000000 : ℝ)] ![(22208086178867/50000000000000 : ℝ), (21535532794679/50000000000000 : ℝ), (12512762031703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379479699/10000000000 : ℝ)|^2169 ≤ (22208086178867/50000000000000 : ℝ)^1657
        have hw : |(5379479699/10000000000 : ℝ)|=(5379479699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328410771/625000000 : ℝ)|^2169 ≤ (21535532794679/50000000000000 : ℝ)^1657
        have hw : |(328410771/625000000 : ℝ)|=(328410771/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1021871089/5000000000 : ℝ)|^2169 ≤ (12512762031703/100000000000000 : ℝ)^1657
        have hw : |(-1021871089/5000000000 : ℝ)|=(1021871089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_box_15 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (828354757/2000000000 : ℝ)*x 0 + (1102143911/2500000000 : ℝ)*x 1 + (220428783/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (828354757/2000000000 : ℝ)^2169 ≤ (31542780092133/100000000000000 : ℝ)^1657 := by
    have hnat : (828354757 : ℕ)^2169*100000000000000^1657 ≤ 31542780092133^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828354757 2000000000 31542780092133 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102143911/2500000000 : ℝ)^2169 ≤ (34228609866547/100000000000000 : ℝ)^1657 := by
    have hnat : (1102143911 : ℕ)^2169*100000000000000^1657 ≤ 34228609866547^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102143911 2500000000 34228609866547 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220428783/500000000 : ℝ)^2169 ≤ (34228610029157/100000000000000 : ℝ)^1657 := by
    have hnat : (220428783 : ℕ)^2169*100000000000000^1657 ≤ 34228610029157^1657*500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220428783 500000000 34228610029157 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(828354757/2000000000 : ℝ), (1102143911/2500000000 : ℝ), (220428783/500000000 : ℝ)] ![(31542780092133/100000000000000 : ℝ), (34228609866547/100000000000000 : ℝ), (34228610029157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(828354757/2000000000 : ℝ)|^2169 ≤ (31542780092133/100000000000000 : ℝ)^1657
        have hw : |(828354757/2000000000 : ℝ)|=(828354757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102143911/2500000000 : ℝ)|^2169 ≤ (34228609866547/100000000000000 : ℝ)^1657
        have hw : |(1102143911/2500000000 : ℝ)|=(1102143911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(220428783/500000000 : ℝ)|^2169 ≤ (34228610029157/100000000000000 : ℝ)^1657
        have hw : |(220428783/500000000 : ℝ)|=(220428783/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1378_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(62871/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14753/25000 : ℝ) ∧ (80163/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84491/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1841/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (351/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1841/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (351/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1841/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (351/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1841/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (351/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1841/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (351/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1841/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (351/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (351/3125 : ℝ) ^ (4337/1024 : ℝ) ≤ (9513755209092241/100000000000000000000 : ℝ) := by
    have hpowers : (351/3125 : ℝ)^4337 ≤ (9513755209092241/100000000000000000000 : ℝ)^1024 := by
      have hnat : (351 : ℕ)^4337*100000000000000000000^1024 ≤ 9513755209092241^1024*3125^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        351 3125 9513755209092241 100000000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (351/3125 : ℝ)) (X := (9513755209092241/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1841/12500 : ℝ) ^ (4337/1024 : ℝ) ≤ (2997757096680849/10000000000000000000 : ℝ) := by
    have hpowers : (1841/12500 : ℝ)^4337 ≤ (2997757096680849/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1841 : ℕ)^4337*10000000000000000000^1024 ≤ 2997757096680849^1024*12500^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1841 12500 2997757096680849 10000000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1841/12500 : ℝ)) (X := (2997757096680849/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009513755209092241/50000000000000000000 : ℝ) ≤ (10000449221923403/10000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (50009513755209092241/50000000000000000000 : ℝ)^1024 ≤ (10000449221923403/10000000000000000 : ℝ)^4337 := by
      have hnat : (50009513755209092241 : ℕ)^1024*10000000000000000^4337 ≤ 10000449221923403^4337*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009513755209092241 50000000000000000000 10000449221923403 10000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000449221923403/10000000000000000 : ℝ)) (X := (50009513755209092241/50000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039491326175900731/100000000000000000000 : ℝ) ≤ (2500233070208457/2500000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (100039491326175900731/100000000000000000000 : ℝ)^1024 ≤ (2500233070208457/2500000000000000 : ℝ)^4337 := by
      have hnat : (100039491326175900731 : ℕ)^1024*2500000000000000^4337 ≤ 2500233070208457^4337*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039491326175900731 100000000000000000000 2500233070208457 2500000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500233070208457/2500000000000000 : ℝ)) (X := (100039491326175900731/100000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002997757096680849/5000000000000000000 : ℝ) ≤ (10001415339744253/10000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (5002997757096680849/5000000000000000000 : ℝ)^1024 ≤ (10001415339744253/10000000000000000 : ℝ)^4337 := by
      have hnat : (5002997757096680849 : ℕ)^1024*10000000000000000^4337 ≤ 10001415339744253^4337*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002997757096680849 5000000000000000000 10001415339744253 10000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001415339744253/10000000000000000 : ℝ)) (X := (5002997757096680849/5000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9513755209092241/100000000000000000000 : ℝ) ≤ ((4368839880560053711/4370000000000000000 : ℝ)+2*(19322356417/13984000000000 : ℝ)*(351/3125 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (4368839880560053711/4370000000000000000 : ℝ)+2*(19322356417/13984000000000 : ℝ)*(351/3125 : ℝ)=(10000449221923403/10000000000000000 : ℝ) by norm_num, show 1+2*(9513755209092241/100000000000000000000 : ℝ)=(50009513755209092241/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2997757096680849/10000000000000000000 : ℝ)+(9513755209092241/100000000000000000000 : ℝ) ≤ ((4368839880560053711/4370000000000000000 : ℝ)+(19322356417/13984000000000 : ℝ)*((1841/12500 : ℝ)+(351/3125 : ℝ)))^(4337/1024 : ℝ) := by
    rw [show (4368839880560053711/4370000000000000000 : ℝ)+(19322356417/13984000000000 : ℝ)*((1841/12500 : ℝ)+(351/3125 : ℝ))=(2500233070208457/2500000000000000 : ℝ) by norm_num, show 1+(2997757096680849/10000000000000000000 : ℝ)+(9513755209092241/100000000000000000000 : ℝ)=(100039491326175900731/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2997757096680849/10000000000000000000 : ℝ) ≤ ((4368839880560053711/4370000000000000000 : ℝ)+2*(19322356417/13984000000000 : ℝ)*(1841/12500 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (4368839880560053711/4370000000000000000 : ℝ)+2*(19322356417/13984000000000 : ℝ)*(1841/12500 : ℝ)=(10001415339744253/10000000000000000 : ℝ) by norm_num, show 1+2*(2997757096680849/10000000000000000000 : ℝ)=(5002997757096680849/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4368839880560053711/4370000000000000000 : ℝ)*(X 1 0+X 2 0)+(19322356417/13984000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (351/3125 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (4368839880560053711/4370000000000000000 : ℝ)) (alpha := (19322356417/13984000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4368839880560053711/4370000000000000000 : ℝ)*(X 0 1+X 2 1)+(19322356417/13984000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (351/3125 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (4368839880560053711/4370000000000000000 : ℝ)) (alpha := (19322356417/13984000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4368839880560053711/4370000000000000000 : ℝ)*(X 0 2+X 1 2)+(19322356417/13984000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (351/3125 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (4368839880560053711/4370000000000000000 : ℝ)) (alpha := (19322356417/13984000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-92441559/500000000 : ℝ)*X 0 0+(2694212769/5000000000 : ℝ)*X 0 1+(5388425589/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642803927/5000000000 : ℝ)*X 1 0+(-397973079/2000000000 : ℝ)*X 1 1+(673553199/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1321401939/2500000000 : ℝ)*X 2 0+(5388425691/10000000000 : ℝ)*X 2 1+(-1989865393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2232330887/5000000000 : ℝ)*X 0 0+(4247423849/10000000000 : ℝ)*X 0 1+(2123712027/5000000000 : ℝ)*X 0 2+(2232330887/5000000000 : ℝ)*X 1 0+(4247423849/10000000000 : ℝ)*X 1 1+(2123712027/5000000000 : ℝ)*X 1 2+(2232330887/5000000000 : ℝ)*X 2 0+(4247423849/10000000000 : ℝ)*X 2 1+(2123712027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2180468167/10000000000 : ℝ)*X 0 0+(164552137/312500000 : ℝ)*X 0 1+(1316417113/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((335731227/625000000 : ℝ)*X 1 0+(-2039369521/10000000000 : ℝ)*X 1 1+(658208587/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2685850051/5000000000 : ℝ)*X 2 0+(2632834107/5000000000 : ℝ)*X 2 1+(-407873907/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4168951873/10000000000 : ℝ)*X 0 0+(2197613211/5000000000 : ℝ)*X 0 1+(219761327/500000000 : ℝ)*X 0 2+(4168951873/10000000000 : ℝ)*X 1 0+(2197613211/5000000000 : ℝ)*X 1 1+(219761327/500000000 : ℝ)*X 1 2+(4168951873/10000000000 : ℝ)*X 2 0+(2197613211/5000000000 : ℝ)*X 2 1+(219761327/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2110734563/10000000000 : ℝ)*X 0 0+(5180992037/10000000000 : ℝ)*X 0 1+(5402427867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((527578303/1000000000 : ℝ)*X 1 0+(-396817791/2000000000 : ℝ)*X 1 1+(5402427759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((263789131/500000000 : ℝ)*X 2 0+(5402427913/10000000000 : ℝ)*X 2 1+(-19840893/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((449783439/1000000000 : ℝ)*X 0 0+(1057637409/2500000000 : ℝ)*X 0 1+(4230551071/10000000000 : ℝ)*X 0 2+(449783439/1000000000 : ℝ)*X 1 0+(1057637409/2500000000 : ℝ)*X 1 1+(4230551071/10000000000 : ℝ)*X 1 2+(449783439/1000000000 : ℝ)*X 2 0+(1057637409/2500000000 : ℝ)*X 2 1+(4230551071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-119927167/625000000 : ℝ)*X 0 0+(5470975279/10000000000 : ℝ)*X 0 1+(1050914437/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1344869923/2500000000 : ℝ)*X 1 0+(-2043742087/10000000000 : ℝ)*X 1 1+(5254572411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5379479699/10000000000 : ℝ)*X 2 0+(328410771/625000000 : ℝ)*X 2 1+(-1021871089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((828354757/2000000000 : ℝ)*X 0 0+(1102143911/2500000000 : ℝ)*X 0 1+(220428783/500000000 : ℝ)*X 0 2+(828354757/2000000000 : ℝ)*X 1 0+(1102143911/2500000000 : ℝ)*X 1 1+(220428783/500000000 : ℝ)*X 1 2+(828354757/2000000000 : ℝ)*X 2 0+(1102143911/2500000000 : ℝ)*X 2 1+(220428783/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62871/100000 : ℝ) ≤ (-3614947837831775505025506563487/5750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10257459/50000000000000 : ℝ)*(lower2) + (15985161/50000000000000 : ℝ)*(upper4) + (2384067/2500000000000 : ℝ)*(upper5) + (1480413335461453/50000000000000 : ℝ)*(major0) + (1480413335461453/50000000000000 : ℝ)*(major1) + (1480413335461453/50000000000000 : ℝ)*(major2) + (11299640369/100000000000000 : ℝ)*(sp2) + (3111029809/100000000000000 : ℝ)*(sp3) + (4046450379993511/100000000000000 : ℝ)*(sp4) + (4046401435243397/100000000000000 : ℝ)*(sp5) + (2023221042417371/50000000000000 : ℝ)*(sp6) + (474038266422657/25000000000000 : ℝ)*(sp7) + (1877801/62500000000 : ℝ)*(sp8) + (10389846343/20000000000000 : ℝ)*(sp13) + (474039044180109/25000000000000 : ℝ)*(f.failure) + (505806673059389/12500000000000 : ℝ)*(f.sum) + (17553007783699/1748000000000000000000000000 : ℝ)*base66 + (1510743070404335417/218500000000000000000000000000000 : ℝ)*base68 + (1712788206198835417/218500000000000000000000000000000 : ℝ)*base70 + (1866409900544835417/218500000000000000000000000000000 : ℝ)*base72 + (1064986483023/349600000000000000000000000 : ℝ)*base74 + (2683507887791335417/218500000000000000000000000000000 : ℝ)*base76 + (1278969146678835417/218500000000000000000000000000000 : ℝ)*base78 + (169532242849835417/218500000000000000000000000000000 : ℝ)*base80 + (5094829198107/1748000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (11505931/1250000000000000000000 : ℝ)*base90 + (11505931/1250000000000000000000 : ℝ)*base92 + (11505931/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (14753/25000 : ℝ) ≤ (1031567918852654422596936147/1748000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5892583/20000000000000 : ℝ)*(lower1) + (8481661/100000000000000 : ℝ)*(upper2) + (12322639/100000000000000 : ℝ)*(lower4) + (1515359207463913/50000000000000 : ℝ)*(major0) + (1515359207463913/50000000000000 : ℝ)*(major1) + (1515359207463913/50000000000000 : ℝ)*(major2) + (128151457793779/3125000000000 : ℝ)*(sp0) + (2050424342360603/50000000000000 : ℝ)*(sp1) + (820169286637681/20000000000000 : ℝ)*(sp2) + (1940914877344761/100000000000000 : ℝ)*(sp3) + (445727959/50000000000000 : ℝ)*(sp5) + (3142988719/100000000000000 : ℝ)*(sp6) + (196400037/20000000000000 : ℝ)*(sp7) + (2926776197/100000000000000 : ℝ)*(sp12) + (970457929672473/50000000000000 : ℝ)*(f.failure) + (1025212394044281/25000000000000 : ℝ)*(f.sum) + (2982938786509/349600000000000000000000000 : ℝ)*base65 + (808555954553956357/218500000000000000000000000000000 : ℝ)*base68 + (550811528986456357/218500000000000000000000000000000 : ℝ)*base70 + (946149759535543643/218500000000000000000000000000000 : ℝ)*base71 + (2667435442623/1748000000000000000000000000 : ℝ)*base74 + (1931300435318043643/218500000000000000000000000000000 : ℝ)*base75 + (3389931454202543643/218500000000000000000000000000000 : ℝ)*base77 + (230723416992956357/218500000000000000000000000000000 : ℝ)*base80 + (4629383044067/1748000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (7437407/2500000000000000000000 : ℝ)*base90 + (7437407/2500000000000000000000 : ℝ)*base92 + (7437407/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80163/100000 : ℝ) ≤ (21895064096881518255248120282193/27312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (236128679/100000000000000 : ℝ)*(upper0) + (106782111/50000000000000 : ℝ)*(upper2) + (68174549/100000000000000 : ℝ)*(lower5) + (835308562531071/25000000000000 : ℝ)*(major0) + (835308562531071/25000000000000 : ℝ)*(major1) + (835308562531071/25000000000000 : ℝ)*(major2) + (14457950653/50000000000000 : ℝ)*(sp1) + (45473297967/100000000000000 : ℝ)*(sp3) + (2499617579/100000000000000 : ℝ)*(sp4) + (1128991481105919/25000000000000 : ℝ)*(sp8) + (4515943233150893/100000000000000 : ℝ)*(sp9) + (22579860745261/500000000000 : ℝ)*(sp10) + (8358317238659/390625000000 : ℝ)*(sp11) + (1818853/48828125000 : ℝ)*(sp12) + (2139774686394671/100000000000000 : ℝ)*(f.failure) + (22579860745261/500000000000 : ℝ)*(f.sum) + (897324467471/874000000000000000000000000 : ℝ)*base66 + (1729474300034291981/109250000000000000000000000000000 : ℝ)*base67 + (771640486582458019/109250000000000000000000000000000 : ℝ)*base70 + (965352698364958019/109250000000000000000000000000000 : ℝ)*base72 + (14538013998327/874000000000000000000000000 : ℝ)*base73 + (801200532098208019/109250000000000000000000000000000 : ℝ)*base76 + (1296550725160458019/109250000000000000000000000000000 : ℝ)*base78 + (1126803025168708019/109250000000000000000000000000000 : ℝ)*base80 + (1502321105513/874000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (43703911/5000000000000000000000 : ℝ)*base89 + (43703911/5000000000000000000000 : ℝ)*base91 + (43703911/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84491/100000 : ℝ) ≤ (-92303977063101158114875413390813/109250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4083483/20000000000000 : ℝ)*(lower1) + (8385283/10000000000000 : ℝ)*(upper3) + (1925107/12500000000000 : ℝ)*(lower4) + (3532031/10000000000000 : ℝ)*(upper5) + (1689061070949987/50000000000000 : ℝ)*(major0) + (1689061070949987/50000000000000 : ℝ)*(major1) + (1689061070949987/50000000000000 : ℝ)*(major2) + (148300247/100000000000000 : ℝ)*(sp4) + (11977202869/50000000000000 : ℝ)*(sp6) + (11446562739/50000000000000 : ℝ)*(sp7) + (4621008832336071/100000000000000 : ℝ)*(sp12) + (2310504490318159/50000000000000 : ℝ)*(sp13) + (231049251311529/5000000000000 : ℝ)*(sp14) + (2163375332101631/100000000000000 : ℝ)*(sp15) + (2163398225227109/100000000000000 : ℝ)*(f.failure) + (2310504490318159/50000000000000 : ℝ)*(f.sum) + (1722012159231/1748000000000000000000000000 : ℝ)*base65 + (2508049493411189257/218500000000000000000000000000000 : ℝ)*base67 + (2357318225004189257/218500000000000000000000000000000 : ℝ)*base69 + (2512466919273189257/218500000000000000000000000000000 : ℝ)*base71 + (6420288512777/1748000000000000000000000000 : ℝ)*base74 + (2250924037702689257/218500000000000000000000000000000 : ℝ)*base75 + (2545607548433189257/218500000000000000000000000000000 : ℝ)*base77 + (3023104870043689257/218500000000000000000000000000000 : ℝ)*base79 + (2694327704917/349600000000000000000000000 : ℝ)*base82 + (66778931/5000000000000000000000 : ℝ)*base90 + (66778931/5000000000000000000000 : ℝ)*base92 + (66778931/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1378_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62871/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14753/25000 : ℝ) else (80163/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84491/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1378_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1378_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62871/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14753/25000 : ℝ) else (80163/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84491/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1378_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1378_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1378_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62871/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14753/25000 : ℝ) else (80163/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84491/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1378_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
