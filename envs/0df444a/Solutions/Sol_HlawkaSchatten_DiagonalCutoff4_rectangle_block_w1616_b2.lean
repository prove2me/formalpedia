-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1616_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:52:33.719014+00:00
-- url     : https://prove2.me/submissions/ac55f88d-5de3-4ed1-963c-f633f1692ee4

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
theorem support_rectangle_w1616_box_0 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-709225639/5000000000 : ℝ)*x 0 + (5416565477/10000000000 : ℝ)*x 1 + (2708282767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (709225639/5000000000 : ℝ)^4783 ≤ (4166081436099/50000000000000 : ℝ)^3759 := by
    have hnat : (709225639 : ℕ)^4783*50000000000000^3759 ≤ 4166081436099^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709225639 5000000000 4166081436099 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416565477/10000000000 : ℝ)^4783 ≤ (4583391824729/10000000000000 : ℝ)^3759 := by
    have hnat : (5416565477 : ℕ)^4783*10000000000000^3759 ≤ 4583391824729^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416565477 10000000000 4583391824729 10000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708282767/5000000000 : ℝ)^4783 ≤ (45833918861003/100000000000000 : ℝ)^3759 := by
    have hnat : (2708282767 : ℕ)^4783*100000000000000^3759 ≤ 45833918861003^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708282767 5000000000 45833918861003 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-709225639/5000000000 : ℝ), (5416565477/10000000000 : ℝ), (2708282767/5000000000 : ℝ)] ![(4166081436099/50000000000000 : ℝ), (4583391824729/10000000000000 : ℝ), (45833918861003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-709225639/5000000000 : ℝ)|^4783 ≤ (4166081436099/50000000000000 : ℝ)^3759
        have hw : |(-709225639/5000000000 : ℝ)|=(709225639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416565477/10000000000 : ℝ)|^4783 ≤ (4583391824729/10000000000000 : ℝ)^3759
        have hw : |(5416565477/10000000000 : ℝ)|=(5416565477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708282767/5000000000 : ℝ)|^4783 ≤ (45833918861003/100000000000000 : ℝ)^3759
        have hw : |(2708282767/5000000000 : ℝ)|=(2708282767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_1 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625608019/5000000000 : ℝ)*x 0 + (-412664343/2500000000 : ℝ)*x 1 + (5416565581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625608019/5000000000 : ℝ)^4783 ≤ (11015268444437/25000000000000 : ℝ)^3759 := by
    have hnat : (2625608019 : ℕ)^4783*25000000000000^3759 ≤ 11015268444437^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625608019 5000000000 11015268444437 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412664343/2500000000 : ℝ)^4783 ≤ (315781463801/3125000000000 : ℝ)^3759 := by
    have hnat : (412664343 : ℕ)^4783*3125000000000^3759 ≤ 315781463801^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412664343 2500000000 315781463801 3125000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416565581/10000000000 : ℝ)^4783 ≤ (5729239920881/12500000000000 : ℝ)^3759 := by
    have hnat : (5416565581 : ℕ)^4783*12500000000000^3759 ≤ 5729239920881^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416565581 10000000000 5729239920881 12500000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625608019/5000000000 : ℝ), (-412664343/2500000000 : ℝ), (5416565581/10000000000 : ℝ)] ![(11015268444437/25000000000000 : ℝ), (315781463801/3125000000000 : ℝ), (5729239920881/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625608019/5000000000 : ℝ)|^4783 ≤ (11015268444437/25000000000000 : ℝ)^3759
        have hw : |(2625608019/5000000000 : ℝ)|=(2625608019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-412664343/2500000000 : ℝ)|^4783 ≤ (315781463801/3125000000000 : ℝ)^3759
        have hw : |(-412664343/2500000000 : ℝ)|=(412664343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416565581/10000000000 : ℝ)|^4783 ≤ (5729239920881/12500000000000 : ℝ)^3759
        have hw : |(5416565581/10000000000 : ℝ)|=(5416565581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_2 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050243229/2000000000 : ℝ)*x 0 + (5416565401/10000000000 : ℝ)*x 1 + (-825328737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050243229/2000000000 : ℝ)^4783 ≤ (22030537460059/50000000000000 : ℝ)^3759 := by
    have hnat : (1050243229 : ℕ)^4783*50000000000000^3759 ≤ 22030537460059^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050243229 2000000000 22030537460059 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416565401/10000000000 : ℝ)^4783 ≤ (9166783485801/20000000000000 : ℝ)^3759 := by
    have hnat : (5416565401 : ℕ)^4783*20000000000000^3759 ≤ 9166783485801^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416565401 10000000000 9166783485801 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (825328737/5000000000 : ℝ)^4783 ≤ (5052503818079/50000000000000 : ℝ)^3759 := by
    have hnat : (825328737 : ℕ)^4783*50000000000000^3759 ≤ 5052503818079^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825328737 5000000000 5052503818079 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050243229/2000000000 : ℝ), (5416565401/10000000000 : ℝ), (-825328737/5000000000 : ℝ)] ![(22030537460059/50000000000000 : ℝ), (9166783485801/20000000000000 : ℝ), (5052503818079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050243229/2000000000 : ℝ)|^4783 ≤ (22030537460059/50000000000000 : ℝ)^3759
        have hw : |(1050243229/2000000000 : ℝ)|=(1050243229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416565401/10000000000 : ℝ)|^4783 ≤ (9166783485801/20000000000000 : ℝ)^3759
        have hw : |(5416565401/10000000000 : ℝ)|=(5416565401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-825328737/5000000000 : ℝ)|^4783 ≤ (5052503818079/50000000000000 : ℝ)^3759
        have hw : |(-825328737/5000000000 : ℝ)|=(825328737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_3 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2243486939/5000000000 : ℝ)*x 0 + (2040289891/5000000000 : ℝ)*x 1 + (4080579709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2243486939/5000000000 : ℝ)^4783 ≤ (36069589891103/100000000000000 : ℝ)^3759 := by
    have hnat : (2243486939 : ℕ)^4783*100000000000000^3759 ≤ 36069589891103^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243486939 5000000000 36069589891103 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2040289891/5000000000 : ℝ)^4783 ≤ (1997825337833/6250000000000 : ℝ)^3759 := by
    have hnat : (2040289891 : ℕ)^4783*6250000000000^3759 ≤ 1997825337833^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040289891 5000000000 1997825337833 6250000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4080579709/10000000000 : ℝ)^4783 ≤ (3995650584713/12500000000000 : ℝ)^3759 := by
    have hnat : (4080579709 : ℕ)^4783*12500000000000^3759 ≤ 3995650584713^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4080579709 10000000000 3995650584713 12500000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2243486939/5000000000 : ℝ), (2040289891/5000000000 : ℝ), (4080579709/10000000000 : ℝ)] ![(36069589891103/100000000000000 : ℝ), (1997825337833/6250000000000 : ℝ), (3995650584713/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2243486939/5000000000 : ℝ)|^4783 ≤ (36069589891103/100000000000000 : ℝ)^3759
        have hw : |(2243486939/5000000000 : ℝ)|=(2243486939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2040289891/5000000000 : ℝ)|^4783 ≤ (1997825337833/6250000000000 : ℝ)^3759
        have hw : |(2040289891/5000000000 : ℝ)|=(2040289891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4080579709/10000000000 : ℝ)|^4783 ≤ (3995650584713/12500000000000 : ℝ)^3759
        have hw : |(4080579709/10000000000 : ℝ)|=(4080579709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_4 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1970889119/10000000000 : ℝ)*x 0 + (5214434453/10000000000 : ℝ)*x 1 + (651804301/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1970889119/10000000000 : ℝ)^4783 ≤ (12662489292297/100000000000000 : ℝ)^3759 := by
    have hnat : (1970889119 : ℕ)^4783*100000000000000^3759 ≤ 12662489292297^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970889119 10000000000 12662489292297 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214434453/10000000000 : ℝ)^4783 ≤ (43668755586789/100000000000000 : ℝ)^3759 := by
    have hnat : (5214434453 : ℕ)^4783*100000000000000^3759 ≤ 43668755586789^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214434453 10000000000 43668755586789 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651804301/1250000000 : ℝ)^4783 ≤ (5458594388409/12500000000000 : ℝ)^3759 := by
    have hnat : (651804301 : ℕ)^4783*12500000000000^3759 ≤ 5458594388409^3759*1250000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651804301 1250000000 5458594388409 12500000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1970889119/10000000000 : ℝ), (5214434453/10000000000 : ℝ), (651804301/1250000000 : ℝ)] ![(12662489292297/100000000000000 : ℝ), (43668755586789/100000000000000 : ℝ), (5458594388409/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1970889119/10000000000 : ℝ)|^4783 ≤ (12662489292297/100000000000000 : ℝ)^3759
        have hw : |(-1970889119/10000000000 : ℝ)|=(1970889119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214434453/10000000000 : ℝ)|^4783 ≤ (43668755586789/100000000000000 : ℝ)^3759
        have hw : |(5214434453/10000000000 : ℝ)|=(5214434453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651804301/1250000000 : ℝ)|^4783 ≤ (5458594388409/12500000000000 : ℝ)^3759
        have hw : |(651804301/1250000000 : ℝ)|=(651804301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_5 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695301903/5000000000 : ℝ)*x 0 + (-86814347/500000000 : ℝ)*x 1 + (1303608611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695301903/5000000000 : ℝ)^4783 ≤ (11388643499053/25000000000000 : ℝ)^3759 := by
    have hnat : (2695301903 : ℕ)^4783*25000000000000^3759 ≤ 11388643499053^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695301903 5000000000 11388643499053 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86814347/500000000 : ℝ)^4783 ≤ (10776670499227/100000000000000 : ℝ)^3759 := by
    have hnat : (86814347 : ℕ)^4783*100000000000000^3759 ≤ 10776670499227^3759*500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86814347 500000000 10776670499227 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303608611/2500000000 : ℝ)^4783 ≤ (8733751098177/20000000000000 : ℝ)^3759 := by
    have hnat : (1303608611 : ℕ)^4783*20000000000000^3759 ≤ 8733751098177^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303608611 2500000000 8733751098177 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695301903/5000000000 : ℝ), (-86814347/500000000 : ℝ), (1303608611/2500000000 : ℝ)] ![(11388643499053/25000000000000 : ℝ), (10776670499227/100000000000000 : ℝ), (8733751098177/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695301903/5000000000 : ℝ)|^4783 ≤ (11388643499053/25000000000000 : ℝ)^3759
        have hw : |(2695301903/5000000000 : ℝ)|=(2695301903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86814347/500000000 : ℝ)|^4783 ≤ (10776670499227/100000000000000 : ℝ)^3759
        have hw : |(-86814347/500000000 : ℝ)|=(86814347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303608611/2500000000 : ℝ)|^4783 ≤ (8733751098177/20000000000000 : ℝ)^3759
        have hw : |(1303608611/2500000000 : ℝ)|=(1303608611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_6 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390603801/10000000000 : ℝ)*x 0 + (5214434433/10000000000 : ℝ)*x 1 + (-868143481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390603801/10000000000 : ℝ)^4783 ≤ (2847160871403/6250000000000 : ℝ)^3759 := by
    have hnat : (5390603801 : ℕ)^4783*6250000000000^3759 ≤ 2847160871403^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390603801 10000000000 2847160871403 6250000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214434433/10000000000 : ℝ)^4783 ≤ (4366875537367/10000000000000 : ℝ)^3759 := by
    have hnat : (5214434433 : ℕ)^4783*10000000000000^3759 ≤ 4366875537367^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214434433 10000000000 4366875537367 10000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (868143481/5000000000 : ℝ)^4783 ≤ (10776670672973/100000000000000 : ℝ)^3759 := by
    have hnat : (868143481 : ℕ)^4783*100000000000000^3759 ≤ 10776670672973^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868143481 5000000000 10776670672973 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390603801/10000000000 : ℝ), (5214434433/10000000000 : ℝ), (-868143481/5000000000 : ℝ)] ![(2847160871403/6250000000000 : ℝ), (4366875537367/10000000000000 : ℝ), (10776670672973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390603801/10000000000 : ℝ)|^4783 ≤ (2847160871403/6250000000000 : ℝ)^3759
        have hw : |(5390603801/10000000000 : ℝ)|=(5390603801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214434433/10000000000 : ℝ)|^4783 ≤ (4366875537367/10000000000000 : ℝ)^3759
        have hw : |(5214434433/10000000000 : ℝ)|=(5214434433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-868143481/5000000000 : ℝ)|^4783 ≤ (10776670672973/100000000000000 : ℝ)^3759
        have hw : |(-868143481/5000000000 : ℝ)|=(868143481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_7 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (490290109/1250000000 : ℝ)*x 0 + (4362565823/10000000000 : ℝ)*x 1 + (1090641441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490290109/1250000000 : ℝ)^4783 ≤ (15198090821821/50000000000000 : ℝ)^3759 := by
    have hnat : (490290109 : ℕ)^4783*50000000000000^3759 ≤ 15198090821821^3759*1250000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490290109 1250000000 15198090821821 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4362565823/10000000000 : ℝ)^4783 ≤ (278415275743/800000000000 : ℝ)^3759 := by
    have hnat : (4362565823 : ℕ)^4783*800000000000^3759 ≤ 278415275743^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362565823 10000000000 278415275743 800000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090641441/2500000000 : ℝ)^4783 ≤ (34801908868993/100000000000000 : ℝ)^3759 := by
    have hnat : (1090641441 : ℕ)^4783*100000000000000^3759 ≤ 34801908868993^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090641441 2500000000 34801908868993 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(490290109/1250000000 : ℝ), (4362565823/10000000000 : ℝ), (1090641441/2500000000 : ℝ)] ![(15198090821821/50000000000000 : ℝ), (278415275743/800000000000 : ℝ), (34801908868993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(490290109/1250000000 : ℝ)|^4783 ≤ (15198090821821/50000000000000 : ℝ)^3759
        have hw : |(490290109/1250000000 : ℝ)|=(490290109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4362565823/10000000000 : ℝ)|^4783 ≤ (278415275743/800000000000 : ℝ)^3759
        have hw : |(4362565823/10000000000 : ℝ)|=(4362565823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090641441/2500000000 : ℝ)|^4783 ≤ (34801908868993/100000000000000 : ℝ)^3759
        have hw : |(1090641441/2500000000 : ℝ)|=(1090641441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_8 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-231671189/1250000000 : ℝ)*x 0 + (1013980941/2000000000 : ℝ)*x 1 + (5446438467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (231671189/1250000000 : ℝ)^4783 ≤ (11709691186551/100000000000000 : ℝ)^3759 := by
    have hnat : (231671189 : ℕ)^4783*100000000000000^3759 ≤ 11709691186551^3759*1250000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231671189 1250000000 11709691186551 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1013980941/2000000000 : ℝ)^4783 ≤ (21067254747293/50000000000000 : ℝ)^3759 := by
    have hnat : (1013980941 : ℕ)^4783*50000000000000^3759 ≤ 21067254747293^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013980941 2000000000 21067254747293 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446438467/10000000000 : ℝ)^4783 ≤ (11538949826133/25000000000000 : ℝ)^3759 := by
    have hnat : (5446438467 : ℕ)^4783*25000000000000^3759 ≤ 11538949826133^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446438467 10000000000 11538949826133 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-231671189/1250000000 : ℝ), (1013980941/2000000000 : ℝ), (5446438467/10000000000 : ℝ)] ![(11709691186551/100000000000000 : ℝ), (21067254747293/50000000000000 : ℝ), (11538949826133/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-231671189/1250000000 : ℝ)|^4783 ≤ (11709691186551/100000000000000 : ℝ)^3759
        have hw : |(-231671189/1250000000 : ℝ)|=(231671189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1013980941/2000000000 : ℝ)|^4783 ≤ (21067254747293/50000000000000 : ℝ)^3759
        have hw : |(1013980941/2000000000 : ℝ)|=(1013980941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446438467/10000000000 : ℝ)|^4783 ≤ (11538949826133/25000000000000 : ℝ)^3759
        have hw : |(5446438467/10000000000 : ℝ)|=(5446438467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_9 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615306427/5000000000 : ℝ)*x 0 + (-409386481/2500000000 : ℝ)*x 1 + (5446437531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615306427/5000000000 : ℝ)^4783 ≤ (43841224413593/100000000000000 : ℝ)^3759 := by
    have hnat : (2615306427 : ℕ)^4783*100000000000000^3759 ≤ 43841224413593^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615306427 5000000000 43841224413593 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409386481/2500000000 : ℝ)^4783 ≤ (10002986363007/100000000000000 : ℝ)^3759 := by
    have hnat : (409386481 : ℕ)^4783*100000000000000^3759 ≤ 10002986363007^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409386481 2500000000 10002986363007 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446437531/10000000000 : ℝ)^4783 ≤ (9231157842319/20000000000000 : ℝ)^3759 := by
    have hnat : (5446437531 : ℕ)^4783*20000000000000^3759 ≤ 9231157842319^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446437531 10000000000 9231157842319 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615306427/5000000000 : ℝ), (-409386481/2500000000 : ℝ), (5446437531/10000000000 : ℝ)] ![(43841224413593/100000000000000 : ℝ), (10002986363007/100000000000000 : ℝ), (9231157842319/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615306427/5000000000 : ℝ)|^4783 ≤ (43841224413593/100000000000000 : ℝ)^3759
        have hw : |(2615306427/5000000000 : ℝ)|=(2615306427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-409386481/2500000000 : ℝ)|^4783 ≤ (10002986363007/100000000000000 : ℝ)^3759
        have hw : |(-409386481/2500000000 : ℝ)|=(409386481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446437531/10000000000 : ℝ)|^4783 ≤ (9231157842319/20000000000000 : ℝ)^3759
        have hw : |(5446437531/10000000000 : ℝ)|=(5446437531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_10 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230612723/10000000000 : ℝ)*x 0 + (2723219259/5000000000 : ℝ)*x 1 + (-818772367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230612723/10000000000 : ℝ)^4783 ≤ (43841223016487/100000000000000 : ℝ)^3759 := by
    have hnat : (5230612723 : ℕ)^4783*100000000000000^3759 ≤ 43841223016487^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230612723 10000000000 43841223016487 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723219259/5000000000 : ℝ)^4783 ≤ (46155799854467/100000000000000 : ℝ)^3759 := by
    have hnat : (2723219259 : ℕ)^4783*100000000000000^3759 ≤ 46155799854467^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723219259 5000000000 46155799854467 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (818772367/5000000000 : ℝ)^4783 ≤ (5001488556829/50000000000000 : ℝ)^3759 := by
    have hnat : (818772367 : ℕ)^4783*50000000000000^3759 ≤ 5001488556829^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818772367 5000000000 5001488556829 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230612723/10000000000 : ℝ), (2723219259/5000000000 : ℝ), (-818772367/5000000000 : ℝ)] ![(43841223016487/100000000000000 : ℝ), (46155799854467/100000000000000 : ℝ), (5001488556829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230612723/10000000000 : ℝ)|^4783 ≤ (43841223016487/100000000000000 : ℝ)^3759
        have hw : |(5230612723/10000000000 : ℝ)|=(5230612723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723219259/5000000000 : ℝ)|^4783 ≤ (46155799854467/100000000000000 : ℝ)^3759
        have hw : |(2723219259/5000000000 : ℝ)|=(2723219259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-818772367/5000000000 : ℝ)|^4783 ≤ (5001488556829/50000000000000 : ℝ)^3759
        have hw : |(-818772367/5000000000 : ℝ)|=(818772367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_11 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1142007269/2500000000 : ℝ)*x 0 + (2019415249/5000000000 : ℝ)*x 1 + (100970743/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1142007269/2500000000 : ℝ)^4783 ≤ (1845035063497/5000000000000 : ℝ)^3759 := by
    have hnat : (1142007269 : ℕ)^4783*5000000000000^3759 ≤ 1845035063497^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142007269 2500000000 1845035063497 5000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2019415249/5000000000 : ℝ)^4783 ≤ (31549653224213/100000000000000 : ℝ)^3759 := by
    have hnat : (2019415249 : ℕ)^4783*100000000000000^3759 ≤ 31549653224213^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019415249 5000000000 31549653224213 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100970743/250000000 : ℝ)^4783 ≤ (15774822745619/50000000000000 : ℝ)^3759 := by
    have hnat : (100970743 : ℕ)^4783*50000000000000^3759 ≤ 15774822745619^3759*250000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100970743 250000000 15774822745619 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1142007269/2500000000 : ℝ), (2019415249/5000000000 : ℝ), (100970743/250000000 : ℝ)] ![(1845035063497/5000000000000 : ℝ), (31549653224213/100000000000000 : ℝ), (15774822745619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1142007269/2500000000 : ℝ)|^4783 ≤ (1845035063497/5000000000000 : ℝ)^3759
        have hw : |(1142007269/2500000000 : ℝ)|=(1142007269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2019415249/5000000000 : ℝ)|^4783 ≤ (31549653224213/100000000000000 : ℝ)^3759
        have hw : |(2019415249/5000000000 : ℝ)|=(2019415249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100970743/250000000 : ℝ)|^4783 ≤ (15774822745619/50000000000000 : ℝ)^3759
        have hw : |(100970743/250000000 : ℝ)|=(100970743/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_12 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-767329613/5000000000 : ℝ)*x 0 + (5555277861/10000000000 : ℝ)*x 1 + (324660423/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (767329613/5000000000 : ℝ)^4783 ≤ (4605121942049/50000000000000 : ℝ)^3759 := by
    have hnat : (767329613 : ℕ)^4783*50000000000000^3759 ≤ 4605121942049^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767329613 5000000000 4605121942049 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5555277861/10000000000 : ℝ)^4783 ≤ (9466519870647/20000000000000 : ℝ)^3759 := by
    have hnat : (5555277861 : ℕ)^4783*20000000000000^3759 ≤ 9466519870647^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5555277861 10000000000 9466519870647 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324660423/625000000 : ℝ)^4783 ≤ (21728578375541/50000000000000 : ℝ)^3759 := by
    have hnat : (324660423 : ℕ)^4783*50000000000000^3759 ≤ 21728578375541^3759*625000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324660423 625000000 21728578375541 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-767329613/5000000000 : ℝ), (5555277861/10000000000 : ℝ), (324660423/625000000 : ℝ)] ![(4605121942049/50000000000000 : ℝ), (9466519870647/20000000000000 : ℝ), (21728578375541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-767329613/5000000000 : ℝ)|^4783 ≤ (4605121942049/50000000000000 : ℝ)^3759
        have hw : |(-767329613/5000000000 : ℝ)|=(767329613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5555277861/10000000000 : ℝ)|^4783 ≤ (9466519870647/20000000000000 : ℝ)^3759
        have hw : |(5555277861/10000000000 : ℝ)|=(5555277861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(324660423/625000000 : ℝ)|^4783 ≤ (21728578375541/50000000000000 : ℝ)^3759
        have hw : |(324660423/625000000 : ℝ)|=(324660423/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_13 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404312179/10000000000 : ℝ)*x 0 + (-218050609/1250000000 : ℝ)*x 1 + (2597282989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404312179/10000000000 : ℝ)^4783 ≤ (45702028775727/100000000000000 : ℝ)^3759 := by
    have hnat : (5404312179 : ℕ)^4783*100000000000000^3759 ≤ 45702028775727^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404312179 10000000000 45702028775727 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218050609/1250000000 : ℝ)^4783 ≤ (10840822874317/100000000000000 : ℝ)^3759 := by
    have hnat : (218050609 : ℕ)^4783*100000000000000^3759 ≤ 10840822874317^3759*1250000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218050609 1250000000 10840822874317 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597282989/5000000000 : ℝ)^4783 ≤ (43457148341641/100000000000000 : ℝ)^3759 := by
    have hnat : (2597282989 : ℕ)^4783*100000000000000^3759 ≤ 43457148341641^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597282989 5000000000 43457148341641 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404312179/10000000000 : ℝ), (-218050609/1250000000 : ℝ), (2597282989/5000000000 : ℝ)] ![(45702028775727/100000000000000 : ℝ), (10840822874317/100000000000000 : ℝ), (43457148341641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404312179/10000000000 : ℝ)|^4783 ≤ (45702028775727/100000000000000 : ℝ)^3759
        have hw : |(5404312179/10000000000 : ℝ)|=(5404312179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-218050609/1250000000 : ℝ)|^4783 ≤ (10840822874317/100000000000000 : ℝ)^3759
        have hw : |(-218050609/1250000000 : ℝ)|=(218050609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597282989/5000000000 : ℝ)|^4783 ≤ (43457148341641/100000000000000 : ℝ)^3759
        have hw : |(2597282989/5000000000 : ℝ)|=(2597282989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_14 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (108086247/200000000 : ℝ)*x 0 + (1038913227/2000000000 : ℝ)*x 1 + (-1744404427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108086247/200000000 : ℝ)^4783 ≤ (45702030615733/100000000000000 : ℝ)^3759 := by
    have hnat : (108086247 : ℕ)^4783*100000000000000^3759 ≤ 45702030615733^3759*200000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108086247 200000000 45702030615733 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038913227/2000000000 : ℝ)^4783 ≤ (8691430002577/20000000000000 : ℝ)^3759 := by
    have hnat : (1038913227 : ℕ)^4783*20000000000000^3759 ≤ 8691430002577^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038913227 2000000000 8691430002577 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1744404427/10000000000 : ℝ)^4783 ≤ (10840819355449/100000000000000 : ℝ)^3759 := by
    have hnat : (1744404427 : ℕ)^4783*100000000000000^3759 ≤ 10840819355449^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744404427 10000000000 10840819355449 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108086247/200000000 : ℝ), (1038913227/2000000000 : ℝ), (-1744404427/10000000000 : ℝ)] ![(45702030615733/100000000000000 : ℝ), (8691430002577/20000000000000 : ℝ), (10840819355449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108086247/200000000 : ℝ)|^4783 ≤ (45702030615733/100000000000000 : ℝ)^3759
        have hw : |(108086247/200000000 : ℝ)|=(108086247/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1038913227/2000000000 : ℝ)|^4783 ≤ (8691430002577/20000000000000 : ℝ)^3759
        have hw : |(1038913227/2000000000 : ℝ)|=(1038913227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1744404427/10000000000 : ℝ)|^4783 ≤ (10840819355449/100000000000000 : ℝ)^3759
        have hw : |(-1744404427/10000000000 : ℝ)|=(1744404427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_box_15 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1932597603/5000000000 : ℝ)*x 0 + (1097558349/2500000000 : ℝ)*x 1 + (1097558499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1932597603/5000000000 : ℝ)^4783 ≤ (29834008894057/100000000000000 : ℝ)^3759 := by
    have hnat : (1932597603 : ℕ)^4783*100000000000000^3759 ≤ 29834008894057^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932597603 5000000000 29834008894057 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097558349/2500000000 : ℝ)^4783 ≤ (8770748123131/25000000000000 : ℝ)^3759 := by
    have hnat : (1097558349 : ℕ)^4783*25000000000000^3759 ≤ 8770748123131^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097558349 2500000000 8770748123131 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097558499/2500000000 : ℝ)^4783 ≤ (17541499296673/50000000000000 : ℝ)^3759 := by
    have hnat : (1097558499 : ℕ)^4783*50000000000000^3759 ≤ 17541499296673^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097558499 2500000000 17541499296673 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1932597603/5000000000 : ℝ), (1097558349/2500000000 : ℝ), (1097558499/2500000000 : ℝ)] ![(29834008894057/100000000000000 : ℝ), (8770748123131/25000000000000 : ℝ), (17541499296673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1932597603/5000000000 : ℝ)|^4783 ≤ (29834008894057/100000000000000 : ℝ)^3759
        have hw : |(1932597603/5000000000 : ℝ)|=(1932597603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097558349/2500000000 : ℝ)|^4783 ≤ (8770748123131/25000000000000 : ℝ)^3759
        have hw : |(1097558349/2500000000 : ℝ)|=(1097558349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097558499/2500000000 : ℝ)|^4783 ≤ (17541499296673/50000000000000 : ℝ)^3759
        have hw : |(1097558499/2500000000 : ℝ)|=(1097558499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1616_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1633/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5237/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(64939/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58259/100000 : ℝ) ∧ (80553/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17577/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1633/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5237/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1633/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5237/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1633/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5237/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1633/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5237/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1633/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5237/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1633/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5237/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5237/50000 : ℝ) ^ (4779/1024 : ℝ) ≤ (2672224968082589/100000000000000000000 : ℝ) := by
    have hpowers : (5237/50000 : ℝ)^4779 ≤ (2672224968082589/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5237 : ℕ)^4779*100000000000000000000^1024 ≤ 2672224968082589^1024*50000^4779 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5237 50000 2672224968082589 100000000000000000000 4779 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5237/50000 : ℝ)) (X := (2672224968082589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1633/10000 : ℝ) ^ (4779/1024 : ℝ) ≤ (21233064191701407/100000000000000000000 : ℝ) := by
    have hpowers : (1633/10000 : ℝ)^4779 ≤ (21233064191701407/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1633 : ℕ)^4779*100000000000000000000^1024 ≤ 21233064191701407^1024*10000^4779 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1633 10000 21233064191701407 100000000000000000000 4779 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1633/10000 : ℝ)) (X := (21233064191701407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002672224968082589/50000000000000000000 : ℝ) ≤ (5000057256767427/5000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (50002672224968082589/50000000000000000000 : ℝ)^1024 ≤ (5000057256767427/5000000000000000 : ℝ)^4779 := by
      have hnat : (50002672224968082589 : ℕ)^1024*5000000000000000^4779 ≤ 5000057256767427^4779*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002672224968082589 50000000000000000000 5000057256767427 5000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000057256767427/5000000000000000 : ℝ)) (X := (50002672224968082589/50000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25005976322289945999/25000000000000000000 : ℝ) ≤ (500025608618403/500000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (25005976322289945999/25000000000000000000 : ℝ)^1024 ≤ (500025608618403/500000000000000 : ℝ)^4779 := by
      have hnat : (25005976322289945999 : ℕ)^1024*500000000000000^4779 ≤ 500025608618403^4779*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005976322289945999 25000000000000000000 500025608618403 500000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500025608618403/500000000000000 : ℝ)) (X := (25005976322289945999/25000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021233064191701407/50000000000000000000 : ℝ) ≤ (5000454915600633/5000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (50021233064191701407/50000000000000000000 : ℝ)^1024 ≤ (5000454915600633/5000000000000000 : ℝ)^4779 := by
      have hnat : (50021233064191701407 : ℕ)^1024*5000000000000000^4779 ≤ 5000454915600633^4779*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021233064191701407 50000000000000000000 5000454915600633 5000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000454915600633/5000000000000000 : ℝ)) (X := (50021233064191701407/50000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2672224968082589/100000000000000000000 : ℝ) ≤ ((2439680851417587739/2440000000000000000 : ℝ)+2*(66276472201/97600000000000 : ℝ)*(5237/50000 : ℝ))^(4779/1024 : ℝ) := by
    rw [show (2439680851417587739/2440000000000000000 : ℝ)+2*(66276472201/97600000000000 : ℝ)*(5237/50000 : ℝ)=(5000057256767427/5000000000000000 : ℝ) by norm_num, show 1+2*(2672224968082589/100000000000000000000 : ℝ)=(50002672224968082589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21233064191701407/100000000000000000000 : ℝ)+(2672224968082589/100000000000000000000 : ℝ) ≤ ((2439680851417587739/2440000000000000000 : ℝ)+(66276472201/97600000000000 : ℝ)*((1633/10000 : ℝ)+(5237/50000 : ℝ)))^(4779/1024 : ℝ) := by
    rw [show (2439680851417587739/2440000000000000000 : ℝ)+(66276472201/97600000000000 : ℝ)*((1633/10000 : ℝ)+(5237/50000 : ℝ))=(500025608618403/500000000000000 : ℝ) by norm_num, show 1+(21233064191701407/100000000000000000000 : ℝ)+(2672224968082589/100000000000000000000 : ℝ)=(25005976322289945999/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21233064191701407/100000000000000000000 : ℝ) ≤ ((2439680851417587739/2440000000000000000 : ℝ)+2*(66276472201/97600000000000 : ℝ)*(1633/10000 : ℝ))^(4779/1024 : ℝ) := by
    rw [show (2439680851417587739/2440000000000000000 : ℝ)+2*(66276472201/97600000000000 : ℝ)*(1633/10000 : ℝ)=(5000454915600633/5000000000000000 : ℝ) by norm_num, show 1+2*(21233064191701407/100000000000000000000 : ℝ)=(50021233064191701407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2439680851417587739/2440000000000000000 : ℝ)*(X 1 0+X 2 0)+(66276472201/97600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (5237/50000 : ℝ)) (hi := (1633/10000 : ℝ)) (c := (2439680851417587739/2440000000000000000 : ℝ)) (alpha := (66276472201/97600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2439680851417587739/2440000000000000000 : ℝ)*(X 0 1+X 2 1)+(66276472201/97600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (5237/50000 : ℝ)) (hi := (1633/10000 : ℝ)) (c := (2439680851417587739/2440000000000000000 : ℝ)) (alpha := (66276472201/97600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2439680851417587739/2440000000000000000 : ℝ)*(X 0 2+X 1 2)+(66276472201/97600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (5237/50000 : ℝ)) (hi := (1633/10000 : ℝ)) (c := (2439680851417587739/2440000000000000000 : ℝ)) (alpha := (66276472201/97600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-709225639/5000000000 : ℝ)*X 0 0+(5416565477/10000000000 : ℝ)*X 0 1+(2708282767/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2625608019/5000000000 : ℝ)*X 1 0+(-412664343/2500000000 : ℝ)*X 1 1+(5416565581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1050243229/2000000000 : ℝ)*X 2 0+(5416565401/10000000000 : ℝ)*X 2 1+(-825328737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2243486939/5000000000 : ℝ)*X 0 0+(2040289891/5000000000 : ℝ)*X 0 1+(4080579709/10000000000 : ℝ)*X 0 2+(2243486939/5000000000 : ℝ)*X 1 0+(2040289891/5000000000 : ℝ)*X 1 1+(4080579709/10000000000 : ℝ)*X 1 2+(2243486939/5000000000 : ℝ)*X 2 0+(2040289891/5000000000 : ℝ)*X 2 1+(4080579709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1970889119/10000000000 : ℝ)*X 0 0+(5214434453/10000000000 : ℝ)*X 0 1+(651804301/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2695301903/5000000000 : ℝ)*X 1 0+(-86814347/500000000 : ℝ)*X 1 1+(1303608611/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5390603801/10000000000 : ℝ)*X 2 0+(5214434433/10000000000 : ℝ)*X 2 1+(-868143481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((490290109/1250000000 : ℝ)*X 0 0+(4362565823/10000000000 : ℝ)*X 0 1+(1090641441/2500000000 : ℝ)*X 0 2+(490290109/1250000000 : ℝ)*X 1 0+(4362565823/10000000000 : ℝ)*X 1 1+(1090641441/2500000000 : ℝ)*X 1 2+(490290109/1250000000 : ℝ)*X 2 0+(4362565823/10000000000 : ℝ)*X 2 1+(1090641441/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-231671189/1250000000 : ℝ)*X 0 0+(1013980941/2000000000 : ℝ)*X 0 1+(5446438467/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2615306427/5000000000 : ℝ)*X 1 0+(-409386481/2500000000 : ℝ)*X 1 1+(5446437531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230612723/10000000000 : ℝ)*X 2 0+(2723219259/5000000000 : ℝ)*X 2 1+(-818772367/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1142007269/2500000000 : ℝ)*X 0 0+(2019415249/5000000000 : ℝ)*X 0 1+(100970743/250000000 : ℝ)*X 0 2+(1142007269/2500000000 : ℝ)*X 1 0+(2019415249/5000000000 : ℝ)*X 1 1+(100970743/250000000 : ℝ)*X 1 2+(1142007269/2500000000 : ℝ)*X 2 0+(2019415249/5000000000 : ℝ)*X 2 1+(100970743/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-767329613/5000000000 : ℝ)*X 0 0+(5555277861/10000000000 : ℝ)*X 0 1+(324660423/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5404312179/10000000000 : ℝ)*X 1 0+(-218050609/1250000000 : ℝ)*X 1 1+(2597282989/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((108086247/200000000 : ℝ)*X 2 0+(1038913227/2000000000 : ℝ)*X 2 1+(-1744404427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1932597603/5000000000 : ℝ)*X 0 0+(1097558349/2500000000 : ℝ)*X 0 1+(1097558499/2500000000 : ℝ)*X 0 2+(1932597603/5000000000 : ℝ)*X 1 0+(1097558349/2500000000 : ℝ)*X 1 1+(1097558499/2500000000 : ℝ)*X 1 2+(1932597603/5000000000 : ℝ)*X 2 0+(1097558349/2500000000 : ℝ)*X 2 1+(1097558499/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-64939/100000 : ℝ) ≤ (-79222314724562845829465973005271/122000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4442787/100000000000000 : ℝ)*(upper0) + (3688989/100000000000000 : ℝ)*(upper1) + (810101/6250000000000 : ℝ)*(upper3) + (356653/100000000000000 : ℝ)*(upper5) + (1693485102002137/100000000000000 : ℝ)*(major0) + (1693485102002137/100000000000000 : ℝ)*(major1) + (1693485102002137/100000000000000 : ℝ)*(major2) + (87326291/100000000000000 : ℝ)*(sp1) + (34672409/12500000000000 : ℝ)*(sp3) + (608610779209133/25000000000000 : ℝ)*(sp4) + (1217221541834513/50000000000000 : ℝ)*(sp5) + (2434443170995317/100000000000000 : ℝ)*(sp6) + (779337757449/80000000000 : ℝ)*(sp7) + (27079393/50000000000000 : ℝ)*(sp8) + (974172474190523/100000000000000 : ℝ)*(f.failure) + (2434443170995317/100000000000000 : ℝ)*(f.sum) + (23400996402657/4880000000000000000000000000 : ℝ)*base65 + (3131251651581423243/244000000000000000000000000000000 : ℝ)*base67 + (3188040514602576757/244000000000000000000000000000000 : ℝ)*base70 + (77573377418576757/244000000000000000000000000000000 : ℝ)*base72 + (28847756254977/4880000000000000000000000000 : ℝ)*base73 + (899274856129423243/244000000000000000000000000000000 : ℝ)*base75 + (305769961750576757/244000000000000000000000000000000 : ℝ)*base78 + (3470955281358576757/244000000000000000000000000000000 : ℝ)*base80 + (9236642789183/4880000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (18750863/2500000000000000000000 : ℝ)*base89 + (18750863/2500000000000000000000 : ℝ)*base91 + (18750863/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58259/100000 : ℝ) ≤ (35539466659166928187165318682313/61000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1391589/50000000000000 : ℝ)*(lower0) + (2205647/100000000000000 : ℝ)*(upper2) + (12185941/100000000000000 : ℝ)*(lower5) + (1779110215869411/100000000000000 : ℝ)*(major0) + (1779110215869411/100000000000000 : ℝ)*(major1) + (1779110215869411/100000000000000 : ℝ)*(major2) + (251537130789759/10000000000000 : ℝ)*(sp0) + (1257685333320741/50000000000000 : ℝ)*(sp1) + (1257682983205541/50000000000000 : ℝ)*(sp2) + (511714028472479/50000000000000 : ℝ)*(sp3) + (1214819591/100000000000000 : ℝ)*(sp5) + (19748539/100000000000000 : ℝ)*(sp7) + (591504999/10000000000000 : ℝ)*(sp10) + (573563483/100000000000000 : ℝ)*(sp12) + (511714038346749/50000000000000 : ℝ)*(f.failure) + (157210742591317/6250000000000 : ℝ)*(f.sum) + (24878012848091/4880000000000000000000000000 : ℝ)*base65 + (1656034815374973271/244000000000000000000000000000000 : ℝ)*base68 + (655962790481026729/244000000000000000000000000000000 : ℝ)*base69 + (632442954113026729/244000000000000000000000000000000 : ℝ)*base71 + (6755030187691/4880000000000000000000000000 : ℝ)*base73 + (973497694633026729/244000000000000000000000000000000 : ℝ)*base75 + (2179917794601026729/244000000000000000000000000000000 : ℝ)*base77 + (2271819012829026729/244000000000000000000000000000000 : ℝ)*base79 + (7727996872411/4880000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (6752169/1250000000000000000000 : ℝ)*base89 + (6752169/1250000000000000000000 : ℝ)*base91 + (6752169/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80553/100000 : ℝ) ≤ (3931097156137601646126588621/4880000000000000000000000000 : ℝ) := by norm_num
    linear_combination (239919/2000000000000 : ℝ)*(lower2) + (60455493/100000000000000 : ℝ)*(lower3) + (222401573/100000000000000 : ℝ)*(upper4) + (1882902509529447/100000000000000 : ℝ)*(major0) + (1882902509529447/100000000000000 : ℝ)*(major1) + (1882902509529447/100000000000000 : ℝ)*(major2) + (11685846613/100000000000000 : ℝ)*(sp1) + (142338159217/100000000000000 : ℝ)*(sp2) + (11969119917/25000000000000 : ℝ)*(sp3) + (9613498359/100000000000000 : ℝ)*(sp4) + (663952337869977/25000000000000 : ℝ)*(sp8) + (1327903639565827/50000000000000 : ℝ)*(sp9) + (53113532536381/2000000000000 : ℝ)*(sp10) + (27077160526749/2500000000000 : ℝ)*(sp11) + (270783574387407/25000000000000 : ℝ)*(f.failure) + (2655818964978267/100000000000000 : ℝ)*(f.sum) + (2878071970513/4880000000000000000000000000 : ℝ)*base66 + (66803482385825333/244000000000000000000000000000000 : ℝ)*base67 + (1576922793282174667/244000000000000000000000000000000 : ℝ)*base70 + (144277758058174667/244000000000000000000000000000000 : ℝ)*base72 + (5131451157727/4880000000000000000000000000 : ℝ)*base73 + (2495082481825333/244000000000000000000000000000000 : ℝ)*base75 + (178907121521825333/244000000000000000000000000000000 : ℝ)*base77 + (239877470214174667/244000000000000000000000000000000 : ℝ)*base80 + (14680832196673/4880000000000000000000000000 : ℝ)*base82 + (3853533/625000000000000000000 : ℝ)*base90 + (3853533/625000000000000000000 : ℝ)*base92 + (3853533/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-17577/20000 : ℝ) ≤ (-26804318511731315932946089879017/30500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4506869/6250000000000 : ℝ)*(lower1) + (12009651/12500000000000 : ℝ)*(lower2) + (54952241/100000000000000 : ℝ)*(lower3) + (8481693/25000000000000 : ℝ)*(upper5) + (481312637762467/25000000000000 : ℝ)*(major0) + (481312637762467/25000000000000 : ℝ)*(major1) + (481312637762467/25000000000000 : ℝ)*(major2) + (118866452563/100000000000000 : ℝ)*(sp5) + (41680449859/50000000000000 : ℝ)*(sp6) + (16582907629/100000000000000 : ℝ)*(sp7) + (1386150275818149/50000000000000 : ℝ)*(sp12) + (1386090842591867/50000000000000 : ℝ)*(sp13) + (138610859536829/5000000000000 : ℝ)*(sp14) + (1107478304727083/100000000000000 : ℝ)*(sp15) + (138436860954339/12500000000000 : ℝ)*(f.failure) + (1386150275818149/50000000000000 : ℝ)*(f.sum) + (1474097030493/1220000000000000000000000000 : ℝ)*base66 + (213791745717267113/61000000000000000000000000000000 : ℝ)*base67 + (1501132941242267113/61000000000000000000000000000000 : ℝ)*base69 + (724372625860267113/61000000000000000000000000000000 : ℝ)*base71 + (3572420205873/1220000000000000000000000000 : ℝ)*base74 + (1482751386682267113/61000000000000000000000000000000 : ℝ)*base75 + (103011988666267113/61000000000000000000000000000000 : ℝ)*base77 + (459651659141267113/61000000000000000000000000000000 : ℝ)*base79 + (14702981445307/1220000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4428041/312500000000000000000 : ℝ)*base90 + (4428041/312500000000000000000 : ℝ)*base92 + (4428041/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1616_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1633/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5237/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64939/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58259/100000 : ℝ) else (80553/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17577/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1616_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1616_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1633/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5237/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64939/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58259/100000 : ℝ) else (80553/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17577/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1616_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1633/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5237/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64939/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58259/100000 : ℝ) else (80553/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17577/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1616_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
