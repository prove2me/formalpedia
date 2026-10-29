-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1325_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:44:52.378269+00:00
-- url     : https://prove2.me/submissions/5e695022-a61e-422a-afe3-e1363b5fa488

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
theorem support_rectangle_w1325_s0_0 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-181923887/1000000000 : ℝ)*x 0 + (600429151/1000000000 : ℝ)*x 1 + (2403418407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181923887/1000000000 : ℝ)^4285 ≤ (10653312354519/100000000000000 : ℝ)^3261 := by
    have hnat : (181923887 : ℕ)^4285*100000000000000^3261 ≤ 10653312354519^3261*1000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181923887 1000000000 10653312354519 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600429151/1000000000 : ℝ)^4285 ≤ (51155889393411/100000000000000 : ℝ)^3261 := by
    have hnat : (600429151 : ℕ)^4285*100000000000000^3261 ≤ 51155889393411^3261*1000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600429151 1000000000 51155889393411 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2403418407/5000000000 : ℝ)^4285 ≤ (3819079823843/10000000000000 : ℝ)^3261 := by
    have hnat : (2403418407 : ℕ)^4285*10000000000000^3261 ≤ 3819079823843^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403418407 5000000000 3819079823843 10000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-181923887/1000000000 : ℝ), (600429151/1000000000 : ℝ), (2403418407/5000000000 : ℝ)] ![(10653312354519/100000000000000 : ℝ), (51155889393411/100000000000000 : ℝ), (3819079823843/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-181923887/1000000000 : ℝ)|^4285 ≤ (10653312354519/100000000000000 : ℝ)^3261
        have hw : |(-181923887/1000000000 : ℝ)|=(181923887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(600429151/1000000000 : ℝ)|^4285 ≤ (51155889393411/100000000000000 : ℝ)^3261
        have hw : |(600429151/1000000000 : ℝ)|=(600429151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2403418407/5000000000 : ℝ)|^4285 ≤ (3819079823843/10000000000000 : ℝ)^3261
        have hw : |(2403418407/5000000000 : ℝ)|=(2403418407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s0_1 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2751858763/5000000000 : ℝ)*x 0 + (-625177983/2500000000 : ℝ)*x 1 + (1201709257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2751858763/5000000000 : ℝ)^4285 ≤ (11406660429461/25000000000000 : ℝ)^3261 := by
    have hnat : (2751858763 : ℕ)^4285*25000000000000^3261 ≤ 11406660429461^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751858763 5000000000 11406660429461 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625177983/2500000000 : ℝ)^4285 ≤ (8091278894187/50000000000000 : ℝ)^3261 := by
    have hnat : (625177983 : ℕ)^4285*50000000000000^3261 ≤ 8091278894187^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625177983 2500000000 8091278894187 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1201709257/2500000000 : ℝ)^4285 ≤ (4773850059073/12500000000000 : ℝ)^3261 := by
    have hnat : (1201709257 : ℕ)^4285*12500000000000^3261 ≤ 4773850059073^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201709257 2500000000 4773850059073 12500000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2751858763/5000000000 : ℝ), (-625177983/2500000000 : ℝ), (1201709257/2500000000 : ℝ)] ![(11406660429461/25000000000000 : ℝ), (8091278894187/50000000000000 : ℝ), (4773850059073/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2751858763/5000000000 : ℝ)|^4285 ≤ (11406660429461/25000000000000 : ℝ)^3261
        have hw : |(2751858763/5000000000 : ℝ)|=(2751858763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-625177983/2500000000 : ℝ)|^4285 ≤ (8091278894187/50000000000000 : ℝ)^3261
        have hw : |(-625177983/2500000000 : ℝ)|=(625177983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1201709257/2500000000 : ℝ)|^4285 ≤ (4773850059073/12500000000000 : ℝ)^3261
        have hw : |(1201709257/2500000000 : ℝ)|=(1201709257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s0_2 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5503716849/10000000000 : ℝ)*x 0 + (2403418647/5000000000 : ℝ)*x 1 + (-2500712473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5503716849/10000000000 : ℝ)^4285 ≤ (4562663434303/10000000000000 : ℝ)^3261 := by
    have hnat : (5503716849 : ℕ)^4285*10000000000000^3261 ≤ 4562663434303^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503716849 10000000000 4562663434303 10000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2403418647/5000000000 : ℝ)^4285 ≤ (38190803249617/100000000000000 : ℝ)^3261 := by
    have hnat : (2403418647 : ℕ)^4285*100000000000000^3261 ≤ 38190803249617^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403418647 5000000000 38190803249617 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2500712473/10000000000 : ℝ)^4285 ≤ (16182562388617/100000000000000 : ℝ)^3261 := by
    have hnat : (2500712473 : ℕ)^4285*100000000000000^3261 ≤ 16182562388617^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500712473 10000000000 16182562388617 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5503716849/10000000000 : ℝ), (2403418647/5000000000 : ℝ), (-2500712473/10000000000 : ℝ)] ![(4562663434303/10000000000000 : ℝ), (38190803249617/100000000000000 : ℝ), (16182562388617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5503716849/10000000000 : ℝ)|^4285 ≤ (4562663434303/10000000000000 : ℝ)^3261
        have hw : |(5503716849/10000000000 : ℝ)|=(5503716849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2403418647/5000000000 : ℝ)|^4285 ≤ (38190803249617/100000000000000 : ℝ)^3261
        have hw : |(2403418647/5000000000 : ℝ)|=(2403418647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2500712473/10000000000 : ℝ)|^4285 ≤ (16182562388617/100000000000000 : ℝ)^3261
        have hw : |(-2500712473/10000000000 : ℝ)|=(2500712473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s0_3 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4181302903/10000000000 : ℝ)*x 0 + (1553726507/5000000000 : ℝ)*x 1 + (5599574127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4181302903/10000000000 : ℝ)^4285 ≤ (31797878088831/100000000000000 : ℝ)^3261 := by
    have hnat : (4181302903 : ℕ)^4285*100000000000000^3261 ≤ 31797878088831^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4181302903 10000000000 31797878088831 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1553726507/5000000000 : ℝ)^4285 ≤ (5382108570441/25000000000000 : ℝ)^3261 := by
    have hnat : (1553726507 : ℕ)^4285*25000000000000^3261 ≤ 5382108570441^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553726507 5000000000 5382108570441 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5599574127/10000000000 : ℝ)^4285 ≤ (9334737521121/20000000000000 : ℝ)^3261 := by
    have hnat : (5599574127 : ℕ)^4285*20000000000000^3261 ≤ 9334737521121^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5599574127 10000000000 9334737521121 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4181302903/10000000000 : ℝ), (1553726507/5000000000 : ℝ), (5599574127/10000000000 : ℝ)] ![(31797878088831/100000000000000 : ℝ), (5382108570441/25000000000000 : ℝ), (9334737521121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4181302903/10000000000 : ℝ)|^4285 ≤ (31797878088831/100000000000000 : ℝ)^3261
        have hw : |(4181302903/10000000000 : ℝ)|=(4181302903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1553726507/5000000000 : ℝ)|^4285 ≤ (5382108570441/25000000000000 : ℝ)^3261
        have hw : |(1553726507/5000000000 : ℝ)|=(1553726507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5599574127/10000000000 : ℝ)|^4285 ≤ (9334737521121/20000000000000 : ℝ)^3261
        have hw : |(5599574127/10000000000 : ℝ)|=(5599574127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s0_4 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1823785333/10000000000 : ℝ)*x 0 + (4837686739/10000000000 : ℝ)*x 1 + (5972341063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1823785333/10000000000 : ℝ)^4285 ≤ (2137662001151/20000000000000 : ℝ)^3261 := by
    have hnat : (1823785333 : ℕ)^4285*20000000000000^3261 ≤ 2137662001151^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823785333 10000000000 2137662001151 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4837686739/10000000000 : ℝ)^4285 ≤ (38513194693637/100000000000000 : ℝ)^3261 := by
    have hnat : (4837686739 : ℕ)^4285*100000000000000^3261 ≤ 38513194693637^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4837686739 10000000000 38513194693637 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5972341063/10000000000 : ℝ)^4285 ≤ (50798495276721/100000000000000 : ℝ)^3261 := by
    have hnat : (5972341063 : ℕ)^4285*100000000000000^3261 ≤ 50798495276721^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5972341063 10000000000 50798495276721 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1823785333/10000000000 : ℝ), (4837686739/10000000000 : ℝ), (5972341063/10000000000 : ℝ)] ![(2137662001151/20000000000000 : ℝ), (38513194693637/100000000000000 : ℝ), (50798495276721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1823785333/10000000000 : ℝ)|^4285 ≤ (2137662001151/20000000000000 : ℝ)^3261
        have hw : |(-1823785333/10000000000 : ℝ)|=(1823785333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4837686739/10000000000 : ℝ)|^4285 ≤ (38513194693637/100000000000000 : ℝ)^3261
        have hw : |(4837686739/10000000000 : ℝ)|=(4837686739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5972341063/10000000000 : ℝ)|^4285 ≤ (50798495276721/100000000000000 : ℝ)^3261
        have hw : |(5972341063/10000000000 : ℝ)|=(5972341063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s0_5 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1035496829/2000000000 : ℝ)*x 0 + (-667604393/5000000000 : ℝ)*x 1 + (2986170487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035496829/2000000000 : ℝ)^4285 ≤ (42106393145579/100000000000000 : ℝ)^3261 := by
    have hnat : (1035496829 : ℕ)^4285*100000000000000^3261 ≤ 42106393145579^3261*2000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035496829 2000000000 42106393145579 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (667604393/5000000000 : ℝ)^4285 ≤ (7095112554077/100000000000000 : ℝ)^3261 := by
    have hnat : (667604393 : ℕ)^4285*100000000000000^3261 ≤ 7095112554077^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667604393 5000000000 7095112554077 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2986170487/5000000000 : ℝ)^4285 ≤ (12699623570503/25000000000000 : ℝ)^3261 := by
    have hnat : (2986170487 : ℕ)^4285*25000000000000^3261 ≤ 12699623570503^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2986170487 5000000000 12699623570503 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035496829/2000000000 : ℝ), (-667604393/5000000000 : ℝ), (2986170487/5000000000 : ℝ)] ![(42106393145579/100000000000000 : ℝ), (7095112554077/100000000000000 : ℝ), (12699623570503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035496829/2000000000 : ℝ)|^4285 ≤ (42106393145579/100000000000000 : ℝ)^3261
        have hw : |(1035496829/2000000000 : ℝ)|=(1035496829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-667604393/5000000000 : ℝ)|^4285 ≤ (7095112554077/100000000000000 : ℝ)^3261
        have hw : |(-667604393/5000000000 : ℝ)|=(667604393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2986170487/5000000000 : ℝ)|^4285 ≤ (12699623570503/25000000000000 : ℝ)^3261
        have hw : |(2986170487/5000000000 : ℝ)|=(2986170487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s0_6 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2588742087/5000000000 : ℝ)*x 0 + (597234103/1000000000 : ℝ)*x 1 + (-333802163/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588742087/5000000000 : ℝ)^4285 ≤ (42106393455483/100000000000000 : ℝ)^3261 := by
    have hnat : (2588742087 : ℕ)^4285*100000000000000^3261 ≤ 42106393455483^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588742087 5000000000 42106393455483 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597234103/1000000000 : ℝ)^4285 ≤ (6349811863487/12500000000000 : ℝ)^3261 := by
    have hnat : (597234103 : ℕ)^4285*12500000000000^3261 ≤ 6349811863487^3261*1000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597234103 1000000000 6349811863487 12500000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (333802163/2500000000 : ℝ)^4285 ≤ (886888952303/12500000000000 : ℝ)^3261 := by
    have hnat : (333802163 : ℕ)^4285*12500000000000^3261 ≤ 886888952303^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333802163 2500000000 886888952303 12500000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588742087/5000000000 : ℝ), (597234103/1000000000 : ℝ), (-333802163/2500000000 : ℝ)] ![(42106393455483/100000000000000 : ℝ), (6349811863487/12500000000000 : ℝ), (886888952303/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588742087/5000000000 : ℝ)|^4285 ≤ (42106393455483/100000000000000 : ℝ)^3261
        have hw : |(2588742087/5000000000 : ℝ)|=(2588742087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597234103/1000000000 : ℝ)|^4285 ≤ (6349811863487/12500000000000 : ℝ)^3261
        have hw : |(597234103/1000000000 : ℝ)|=(597234103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-333802163/2500000000 : ℝ)|^4285 ≤ (886888952303/12500000000000 : ℝ)^3261
        have hw : |(-333802163/2500000000 : ℝ)|=(333802163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s0_7 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4190764103/10000000000 : ℝ)*x 0 + (2767685221/5000000000 : ℝ)*x 1 + (158697347/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4190764103/10000000000 : ℝ)^4285 ≤ (31892455395789/100000000000000 : ℝ)^3261 := by
    have hnat : (4190764103 : ℕ)^4285*100000000000000^3261 ≤ 31892455395789^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4190764103 10000000000 31892455395789 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2767685221/5000000000 : ℝ)^4285 ≤ (45971759699649/100000000000000 : ℝ)^3261 := by
    have hnat : (2767685221 : ℕ)^4285*100000000000000^3261 ≤ 45971759699649^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2767685221 5000000000 45971759699649 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158697347/500000000 : ℝ)^4285 ≤ (5533946221069/25000000000000 : ℝ)^3261 := by
    have hnat : (158697347 : ℕ)^4285*25000000000000^3261 ≤ 5533946221069^3261*500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158697347 500000000 5533946221069 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4190764103/10000000000 : ℝ), (2767685221/5000000000 : ℝ), (158697347/500000000 : ℝ)] ![(31892455395789/100000000000000 : ℝ), (45971759699649/100000000000000 : ℝ), (5533946221069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4190764103/10000000000 : ℝ)|^4285 ≤ (31892455395789/100000000000000 : ℝ)^3261
        have hw : |(4190764103/10000000000 : ℝ)|=(4190764103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2767685221/5000000000 : ℝ)|^4285 ≤ (45971759699649/100000000000000 : ℝ)^3261
        have hw : |(2767685221/5000000000 : ℝ)|=(2767685221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158697347/500000000 : ℝ)|^4285 ≤ (5533946221069/25000000000000 : ℝ)^3261
        have hw : |(158697347/500000000 : ℝ)|=(158697347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1325_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (643/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13497/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1071/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1071 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1071*1^256 ≤ 0^256*1^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1071/256 : ℝ) ≤ (540904600872406913/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1071 ≤ (540904600872406913/25000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1071*25000000000000000000^256 ≤ 540904600872406913^256*5^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 540904600872406913 25000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (540904600872406913/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1071 := by
      have hnat : (1 : ℕ)^256*1^1071 ≤ 1^1071*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25540904600872406913/25000000000000000000 : ℝ) ≤ (10051296324618513/10000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (25540904600872406913/25000000000000000000 : ℝ)^256 ≤ (10051296324618513/10000000000000000 : ℝ)^1071 := by
      have hnat : (25540904600872406913 : ℕ)^256*10000000000000000^1071 ≤ 10051296324618513^1071*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25540904600872406913 25000000000000000000 10051296324618513 10000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10051296324618513/10000000000000000 : ℝ)) (X := (25540904600872406913/25000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (13040904600872406913/12500000000000000000 : ℝ) ≤ (5051296324618513/5000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (13040904600872406913/12500000000000000000 : ℝ)^256 ≤ (5051296324618513/5000000000000000 : ℝ)^1071 := by
      have hnat : (13040904600872406913 : ℕ)^256*5000000000000000^1071 ≤ 5051296324618513^1071*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13040904600872406913 12500000000000000000 5051296324618513 5000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5051296324618513/5000000000000000 : ℝ)) (X := (13040904600872406913/12500000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(51296324618513/4000000000000000 : ℝ)*(0 : ℝ))^(1071/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(51296324618513/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(540904600872406913/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(51296324618513/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1071/256 : ℝ) := by
    rw [show (1 : ℝ)+(51296324618513/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10051296324618513/10000000000000000 : ℝ) by norm_num, show 1+(540904600872406913/25000000000000000000 : ℝ)+(0 : ℝ)=(25540904600872406913/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(540904600872406913/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(51296324618513/4000000000000000 : ℝ)*(2/5 : ℝ))^(1071/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(51296324618513/4000000000000000 : ℝ)*(2/5 : ℝ)=(5051296324618513/5000000000000000 : ℝ) by norm_num, show 1+2*(540904600872406913/25000000000000000000 : ℝ)=(13040904600872406913/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(51296324618513/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51296324618513/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(51296324618513/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51296324618513/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(51296324618513/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51296324618513/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-181923887/1000000000 : ℝ)*X 0 0+(600429151/1000000000 : ℝ)*X 0 1+(2403418407/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2751858763/5000000000 : ℝ)*X 1 0+(-625177983/2500000000 : ℝ)*X 1 1+(1201709257/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5503716849/10000000000 : ℝ)*X 2 0+(2403418647/5000000000 : ℝ)*X 2 1+(-2500712473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4181302903/10000000000 : ℝ)*X 0 0+(1553726507/5000000000 : ℝ)*X 0 1+(5599574127/10000000000 : ℝ)*X 0 2+(4181302903/10000000000 : ℝ)*X 1 0+(1553726507/5000000000 : ℝ)*X 1 1+(5599574127/10000000000 : ℝ)*X 1 2+(4181302903/10000000000 : ℝ)*X 2 0+(1553726507/5000000000 : ℝ)*X 2 1+(5599574127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1823785333/10000000000 : ℝ)*X 0 0+(4837686739/10000000000 : ℝ)*X 0 1+(5972341063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1035496829/2000000000 : ℝ)*X 1 0+(-667604393/5000000000 : ℝ)*X 1 1+(2986170487/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2588742087/5000000000 : ℝ)*X 2 0+(597234103/1000000000 : ℝ)*X 2 1+(-333802163/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4190764103/10000000000 : ℝ)*X 0 0+(2767685221/5000000000 : ℝ)*X 0 1+(158697347/500000000 : ℝ)*X 0 2+(4190764103/10000000000 : ℝ)*X 1 0+(2767685221/5000000000 : ℝ)*X 1 1+(158697347/500000000 : ℝ)*X 1 2+(4190764103/10000000000 : ℝ)*X 2 0+(2767685221/5000000000 : ℝ)*X 2 1+(158697347/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15374936802021857449227/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66667861/100000000000000 : ℝ)*(base1) + (100010147/10000000000000 : ℝ)*(base19) + (897376419/100000000000000 : ℝ)*(base23) + (180693841/100000000000000 : ℝ)*(upper3) + (10692339/100000000000000 : ℝ)*(upper5) + (24727577958007/4000000000000 : ℝ)*(major0) + (24727577958007/4000000000000 : ℝ)*(major1) + (24727577958007/4000000000000 : ℝ)*(major2) + (417554230292841/50000000000000 : ℝ)*(sp0) + (417555089011109/50000000000000 : ℝ)*(sp1) + (835110280747269/100000000000000 : ℝ)*(sp2) + (200632911329769/50000000000000 : ℝ)*(sp3) + (2784205867/100000000000000 : ℝ)*(sp4) + (1702324783/100000000000000 : ℝ)*(sp7) + (200633795826091/50000000000000 : ℝ)*(f.failure) + (104388897265461/12500000000000 : ℝ)*(f.sum) + (19841754512409/8000000000000000000000000000 : ℝ)*base66 + (76319502367591/16000000000000000000000000000 : ℝ)*base67 + (141538190943591/16000000000000000000000000000 : ℝ)*base69 + (107688670687591/16000000000000000000000000000 : ℝ)*base71 + (27248242752409/8000000000000000000000000000 : ℝ)*base74 + (18009001583591/16000000000000000000000000000 : ℝ)*base75 + (51975987279591/16000000000000000000000000000 : ℝ)*base77 + (55106821519591/16000000000000000000000000000 : ℝ)*base79 + (11054999911591/8000000000000000000000000000 : ℝ)*base81 + (1941573/312500000000000000000 : ℝ)*base90 + (1941573/312500000000000000000 : ℝ)*base92 + (1941573/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (575082024251194845540813/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (680283931/50000000000000 : ℝ)*(base19) + (344959901/25000000000000 : ℝ)*(base23) + (41567771/100000000000000 : ℝ)*(base32) + (186599691/100000000000000 : ℝ)*(upper3) + (7167171/5000000000000 : ℝ)*(upper5) + (326199749640789/50000000000000 : ℝ)*(major0) + (326199749640789/50000000000000 : ℝ)*(major1) + (326199749640789/50000000000000 : ℝ)*(major2) + (379178099/12500000000000 : ℝ)*(sp1) + (652187993/20000000000000 : ℝ)*(sp2) + (440662713075021/50000000000000 : ℝ)*(sp4) + (220330258039347/25000000000000 : ℝ)*(sp5) + (110165098171309/12500000000000 : ℝ)*(sp6) + (42347333915133/10000000000000 : ℝ)*(sp7) + (423473380719101/100000000000000 : ℝ)*(f.failure) + (440662713075021/50000000000000 : ℝ)*(f.sum) + (117268091073243/100000000000000000000000000000 : ℝ)*base66 + (709026970273243/200000000000000000000000000000 : ℝ)*base68 + (1595331759873243/200000000000000000000000000000 : ℝ)*base70 + (677415759073243/200000000000000000000000000000 : ℝ)*base72 + (245646665473243/100000000000000000000000000000 : ℝ)*base74 + (10220351726757/200000000000000000000000000000 : ℝ)*base75 + (241191728726757/200000000000000000000000000000 : ℝ)*base77 + (1505887463326757/200000000000000000000000000000 : ℝ)*base79 + (681193091773243/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3141397/625000000000000000000 : ℝ)*base89 + (3141397/625000000000000000000 : ℝ)*base91 + (3141397/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1325_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (643/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13497/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1325_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1325_s1_0 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-250813589/1250000000 : ℝ)*x 0 + (706230831/1250000000 : ℝ)*x 1 + (5041368139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (250813589/1250000000 : ℝ)^4285 ≤ (12117072307229/100000000000000 : ℝ)^3261 := by
    have hnat : (250813589 : ℕ)^4285*100000000000000^3261 ≤ 12117072307229^3261*1250000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250813589 1250000000 12117072307229 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (706230831/1250000000 : ℝ)^4285 ≤ (11806269217859/25000000000000 : ℝ)^3261 := by
    have hnat : (706230831 : ℕ)^4285*25000000000000^3261 ≤ 11806269217859^3261*1250000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706230831 1250000000 11806269217859 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5041368139/10000000000 : ℝ)^4285 ≤ (40657850811981/100000000000000 : ℝ)^3261 := by
    have hnat : (5041368139 : ℕ)^4285*100000000000000^3261 ≤ 40657850811981^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5041368139 10000000000 40657850811981 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-250813589/1250000000 : ℝ), (706230831/1250000000 : ℝ), (5041368139/10000000000 : ℝ)] ![(12117072307229/100000000000000 : ℝ), (11806269217859/25000000000000 : ℝ), (40657850811981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-250813589/1250000000 : ℝ)|^4285 ≤ (12117072307229/100000000000000 : ℝ)^3261
        have hw : |(-250813589/1250000000 : ℝ)|=(250813589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(706230831/1250000000 : ℝ)|^4285 ≤ (11806269217859/25000000000000 : ℝ)^3261
        have hw : |(706230831/1250000000 : ℝ)|=(706230831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5041368139/10000000000 : ℝ)|^4285 ≤ (40657850811981/100000000000000 : ℝ)^3261
        have hw : |(5041368139/10000000000 : ℝ)|=(5041368139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s1_1 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540749767/1000000000 : ℝ)*x 0 + (-1165842291/5000000000 : ℝ)*x 1 + (2520684131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540749767/1000000000 : ℝ)^4285 ≤ (44581371571409/100000000000000 : ℝ)^3261 := by
    have hnat : (540749767 : ℕ)^4285*100000000000000^3261 ≤ 44581371571409^3261*1000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540749767 1000000000 44581371571409 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1165842291/5000000000 : ℝ)^4285 ≤ (738038815423/5000000000000 : ℝ)^3261 := by
    have hnat : (1165842291 : ℕ)^4285*5000000000000^3261 ≤ 738038815423^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165842291 5000000000 738038815423 5000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2520684131/5000000000 : ℝ)^4285 ≤ (10164463028863/25000000000000 : ℝ)^3261 := by
    have hnat : (2520684131 : ℕ)^4285*25000000000000^3261 ≤ 10164463028863^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2520684131 5000000000 10164463028863 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540749767/1000000000 : ℝ), (-1165842291/5000000000 : ℝ), (2520684131/5000000000 : ℝ)] ![(44581371571409/100000000000000 : ℝ), (738038815423/5000000000000 : ℝ), (10164463028863/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540749767/1000000000 : ℝ)|^4285 ≤ (44581371571409/100000000000000 : ℝ)^3261
        have hw : |(540749767/1000000000 : ℝ)|=(540749767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1165842291/5000000000 : ℝ)|^4285 ≤ (738038815423/5000000000000 : ℝ)^3261
        have hw : |(-1165842291/5000000000 : ℝ)|=(1165842291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2520684131/5000000000 : ℝ)|^4285 ≤ (10164463028863/25000000000000 : ℝ)^3261
        have hw : |(2520684131/5000000000 : ℝ)|=(2520684131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s1_2 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5407497909/10000000000 : ℝ)*x 0 + (5041367801/10000000000 : ℝ)*x 1 + (-2331684857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407497909/10000000000 : ℝ)^4285 ≤ (22290687080273/50000000000000 : ℝ)^3261 := by
    have hnat : (5407497909 : ℕ)^4285*50000000000000^3261 ≤ 22290687080273^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407497909 10000000000 22290687080273 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5041367801/10000000000 : ℝ)^4285 ≤ (40657847230087/100000000000000 : ℝ)^3261 := by
    have hnat : (5041367801 : ℕ)^4285*100000000000000^3261 ≤ 40657847230087^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5041367801 10000000000 40657847230087 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2331684857/10000000000 : ℝ)^4285 ≤ (7380389298009/50000000000000 : ℝ)^3261 := by
    have hnat : (2331684857 : ℕ)^4285*50000000000000^3261 ≤ 7380389298009^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2331684857 10000000000 7380389298009 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407497909/10000000000 : ℝ), (5041367801/10000000000 : ℝ), (-2331684857/10000000000 : ℝ)] ![(22290687080273/50000000000000 : ℝ), (40657847230087/100000000000000 : ℝ), (7380389298009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407497909/10000000000 : ℝ)|^4285 ≤ (22290687080273/50000000000000 : ℝ)^3261
        have hw : |(5407497909/10000000000 : ℝ)|=(5407497909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5041367801/10000000000 : ℝ)|^4285 ≤ (40657847230087/100000000000000 : ℝ)^3261
        have hw : |(5041367801/10000000000 : ℝ)|=(5041367801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2331684857/10000000000 : ℝ)|^4285 ≤ (7380389298009/50000000000000 : ℝ)^3261
        have hw : |(-2331684857/10000000000 : ℝ)|=(2331684857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s1_3 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4295328087/10000000000 : ℝ)*x 0 + (926430667/2500000000 : ℝ)*x 1 + (2486038949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4295328087/10000000000 : ℝ)^4285 ≤ (16471077874703/50000000000000 : ℝ)^3261 := by
    have hnat : (4295328087 : ℕ)^4285*50000000000000^3261 ≤ 16471077874703^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295328087 10000000000 16471077874703 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (926430667/2500000000 : ℝ)^4285 ≤ (27132694667787/100000000000000 : ℝ)^3261 := by
    have hnat : (926430667 : ℕ)^4285*100000000000000^3261 ≤ 27132694667787^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926430667 2500000000 27132694667787 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2486038949/5000000000 : ℝ)^4285 ≤ (39925149558783/100000000000000 : ℝ)^3261 := by
    have hnat : (2486038949 : ℕ)^4285*100000000000000^3261 ≤ 39925149558783^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2486038949 5000000000 39925149558783 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4295328087/10000000000 : ℝ), (926430667/2500000000 : ℝ), (2486038949/5000000000 : ℝ)] ![(16471077874703/50000000000000 : ℝ), (27132694667787/100000000000000 : ℝ), (39925149558783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4295328087/10000000000 : ℝ)|^4285 ≤ (16471077874703/50000000000000 : ℝ)^3261
        have hw : |(4295328087/10000000000 : ℝ)|=(4295328087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(926430667/2500000000 : ℝ)|^4285 ≤ (27132694667787/100000000000000 : ℝ)^3261
        have hw : |(926430667/2500000000 : ℝ)|=(926430667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2486038949/5000000000 : ℝ)|^4285 ≤ (39925149558783/100000000000000 : ℝ)^3261
        have hw : |(2486038949/5000000000 : ℝ)|=(2486038949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s1_4 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-501769381/2500000000 : ℝ)*x 0 + (315568937/625000000 : ℝ)*x 1 + (5641969181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (501769381/2500000000 : ℝ)^4285 ≤ (12121586132623/100000000000000 : ℝ)^3261 := by
    have hnat : (501769381 : ℕ)^4285*100000000000000^3261 ≤ 12121586132623^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501769381 2500000000 12121586132623 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (315568937/625000000 : ℝ)^4285 ≤ (40739839260139/100000000000000 : ℝ)^3261 := by
    have hnat : (315568937 : ℕ)^4285*100000000000000^3261 ≤ 40739839260139^3261*625000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315568937 625000000 40739839260139 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5641969181/10000000000 : ℝ)^4285 ≤ (23569287299113/50000000000000 : ℝ)^3261 := by
    have hnat : (5641969181 : ℕ)^4285*50000000000000^3261 ≤ 23569287299113^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5641969181 10000000000 23569287299113 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-501769381/2500000000 : ℝ), (315568937/625000000 : ℝ), (5641969181/10000000000 : ℝ)] ![(12121586132623/100000000000000 : ℝ), (40739839260139/100000000000000 : ℝ), (23569287299113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-501769381/2500000000 : ℝ)|^4285 ≤ (12121586132623/100000000000000 : ℝ)^3261
        have hw : |(-501769381/2500000000 : ℝ)|=(501769381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(315568937/625000000 : ℝ)|^4285 ≤ (40739839260139/100000000000000 : ℝ)^3261
        have hw : |(315568937/625000000 : ℝ)|=(315568937/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5641969181/10000000000 : ℝ)|^4285 ≤ (23569287299113/50000000000000 : ℝ)^3261
        have hw : |(5641969181/10000000000 : ℝ)|=(5641969181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s1_5 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5249833153/10000000000 : ℝ)*x 0 + (-432770949/2500000000 : ℝ)*x 1 + (176311523/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5249833153/10000000000 : ℝ)^4285 ≤ (42881230664651/100000000000000 : ℝ)^3261 := by
    have hnat : (5249833153 : ℕ)^4285*100000000000000^3261 ≤ 42881230664651^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5249833153 10000000000 42881230664651 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432770949/2500000000 : ℝ)^4285 ≤ (1996039921361/20000000000000 : ℝ)^3261 := by
    have hnat : (432770949 : ℕ)^4285*20000000000000^3261 ≤ 1996039921361^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432770949 2500000000 1996039921361 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176311523/312500000 : ℝ)^4285 ≤ (47138569712763/100000000000000 : ℝ)^3261 := by
    have hnat : (176311523 : ℕ)^4285*100000000000000^3261 ≤ 47138569712763^3261*312500000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176311523 312500000 47138569712763 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5249833153/10000000000 : ℝ), (-432770949/2500000000 : ℝ), (176311523/312500000 : ℝ)] ![(42881230664651/100000000000000 : ℝ), (1996039921361/20000000000000 : ℝ), (47138569712763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5249833153/10000000000 : ℝ)|^4285 ≤ (42881230664651/100000000000000 : ℝ)^3261
        have hw : |(5249833153/10000000000 : ℝ)|=(5249833153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-432770949/2500000000 : ℝ)|^4285 ≤ (1996039921361/20000000000000 : ℝ)^3261
        have hw : |(-432770949/2500000000 : ℝ)|=(432770949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(176311523/312500000 : ℝ)|^4285 ≤ (47138569712763/100000000000000 : ℝ)^3261
        have hw : |(176311523/312500000 : ℝ)|=(176311523/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s1_6 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312458221/2500000000 : ℝ)*x 0 + (5641968569/10000000000 : ℝ)*x 1 + (-1731084419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312458221/2500000000 : ℝ)^4285 ≤ (42881227777469/100000000000000 : ℝ)^3261 := by
    have hnat : (1312458221 : ℕ)^4285*100000000000000^3261 ≤ 42881227777469^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312458221 2500000000 42881227777469 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5641968569/10000000000 : ℝ)^4285 ≤ (23569283939671/50000000000000 : ℝ)^3261 := by
    have hnat : (5641968569 : ℕ)^4285*50000000000000^3261 ≤ 23569283939671^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5641968569 10000000000 23569283939671 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1731084419/10000000000 : ℝ)^4285 ≤ (9980204326449/100000000000000 : ℝ)^3261 := by
    have hnat : (1731084419 : ℕ)^4285*100000000000000^3261 ≤ 9980204326449^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1731084419 10000000000 9980204326449 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312458221/2500000000 : ℝ), (5641968569/10000000000 : ℝ), (-1731084419/10000000000 : ℝ)] ![(42881227777469/100000000000000 : ℝ), (23569283939671/50000000000000 : ℝ), (9980204326449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312458221/2500000000 : ℝ)|^4285 ≤ (42881227777469/100000000000000 : ℝ)^3261
        have hw : |(1312458221/2500000000 : ℝ)|=(1312458221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5641968569/10000000000 : ℝ)|^4285 ≤ (23569283939671/50000000000000 : ℝ)^3261
        have hw : |(5641968569/10000000000 : ℝ)|=(5641968569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1731084419/10000000000 : ℝ)|^4285 ≤ (9980204326449/100000000000000 : ℝ)^3261
        have hw : |(-1731084419/10000000000 : ℝ)|=(1731084419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s1_7 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537063891/1250000000 : ℝ)*x 0 + (309748721/625000000 : ℝ)*x 1 + (1861059089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537063891/1250000000 : ℝ)^4285 ≤ (16477039220041/50000000000000 : ℝ)^3261 := by
    have hnat : (537063891 : ℕ)^4285*50000000000000^3261 ≤ 16477039220041^3261*1250000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537063891 1250000000 16477039220041 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (309748721/625000000 : ℝ)^4285 ≤ (19877688137199/50000000000000 : ℝ)^3261 := by
    have hnat : (309748721 : ℕ)^4285*50000000000000^3261 ≤ 19877688137199^3261*625000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309748721 625000000 19877688137199 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1861059089/5000000000 : ℝ)^4285 ≤ (27290545271939/100000000000000 : ℝ)^3261 := by
    have hnat : (1861059089 : ℕ)^4285*100000000000000^3261 ≤ 27290545271939^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861059089 5000000000 27290545271939 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537063891/1250000000 : ℝ), (309748721/625000000 : ℝ), (1861059089/5000000000 : ℝ)] ![(16477039220041/50000000000000 : ℝ), (19877688137199/50000000000000 : ℝ), (27290545271939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537063891/1250000000 : ℝ)|^4285 ≤ (16477039220041/50000000000000 : ℝ)^3261
        have hw : |(537063891/1250000000 : ℝ)|=(537063891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(309748721/625000000 : ℝ)|^4285 ≤ (19877688137199/50000000000000 : ℝ)^3261
        have hw : |(309748721/625000000 : ℝ)|=(309748721/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1861059089/5000000000 : ℝ)|^4285 ≤ (27290545271939/100000000000000 : ℝ)^3261
        have hw : |(1861059089/5000000000 : ℝ)|=(1861059089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1325_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13497/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (673/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19591/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13497/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (643/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13497/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (643/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13497/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (643/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13497/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (643/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13497/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (643/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13497/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (643/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (643/50000 : ℝ) ^ (1071/256 : ℝ) ≤ (1229793896871/100000000000000000000 : ℝ) := by
    have hpowers : (643/50000 : ℝ)^1071 ≤ (1229793896871/100000000000000000000 : ℝ)^256 := by
      have hnat : (643 : ℕ)^1071*100000000000000000000^256 ≤ 1229793896871^256*50000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        643 50000 1229793896871 100000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (643/50000 : ℝ)) (X := (1229793896871/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hpowhi : (13497/50000 : ℝ) ^ (1071/256 : ℝ) ≤ (417496841922782739/100000000000000000000 : ℝ) := by
    have hpowers : (13497/50000 : ℝ)^1071 ≤ (417496841922782739/100000000000000000000 : ℝ)^256 := by
      have hnat : (13497 : ℕ)^1071*100000000000000000000^256 ≤ 417496841922782739^256*50000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13497 50000 417496841922782739 100000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13497/50000 : ℝ)) (X := (417496841922782739/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000001229793896871/50000000000000000000 : ℝ) ≤ (10000000058791267/10000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (50000001229793896871/50000000000000000000 : ℝ)^256 ≤ (10000000058791267/10000000000000000 : ℝ)^1071 := by
      have hnat : (50000001229793896871 : ℕ)^256*10000000000000000^1071 ≤ 10000000058791267^1071*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000001229793896871 50000000000000000000 10000000058791267 10000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000058791267/10000000000000000 : ℝ)) (X := (50000001229793896871/50000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (10041749807171667961/10000000000000000000 : ℝ) ≤ (10009963598602643/10000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (10041749807171667961/10000000000000000000 : ℝ)^256 ≤ (10009963598602643/10000000000000000 : ℝ)^1071 := by
      have hnat : (10041749807171667961 : ℕ)^256*10000000000000000^1071 ≤ 10009963598602643^1071*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10041749807171667961 10000000000000000000 10009963598602643 10000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009963598602643/10000000000000000 : ℝ)) (X := (10041749807171667961/10000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50417496841922782739/50000000000000000000 : ℝ) ≤ (10019927138414019/10000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (50417496841922782739/50000000000000000000 : ℝ)^256 ≤ (10019927138414019/10000000000000000 : ℝ)^1071 := by
      have hnat : (50417496841922782739 : ℕ)^256*10000000000000000^1071 ≤ 10019927138414019^1071*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50417496841922782739 50000000000000000000 10019927138414019 10000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10019927138414019/10000000000000000 : ℝ)) (X := (50417496841922782739/50000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1229793896871/100000000000000000000 : ℝ) ≤ ((64263593821752758241/64270000000000000000 : ℝ)+2*(622721238211/160675000000000 : ℝ)*(643/50000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (64263593821752758241/64270000000000000000 : ℝ)+2*(622721238211/160675000000000 : ℝ)*(643/50000 : ℝ)=(10000000058791267/10000000000000000 : ℝ) by norm_num, show 1+2*(1229793896871/100000000000000000000 : ℝ)=(50000001229793896871/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(417496841922782739/100000000000000000000 : ℝ)+(1229793896871/100000000000000000000 : ℝ) ≤ ((64263593821752758241/64270000000000000000 : ℝ)+(622721238211/160675000000000 : ℝ)*((13497/50000 : ℝ)+(643/50000 : ℝ)))^(1071/256 : ℝ) := by
    rw [show (64263593821752758241/64270000000000000000 : ℝ)+(622721238211/160675000000000 : ℝ)*((13497/50000 : ℝ)+(643/50000 : ℝ))=(10009963598602643/10000000000000000 : ℝ) by norm_num, show 1+(417496841922782739/100000000000000000000 : ℝ)+(1229793896871/100000000000000000000 : ℝ)=(10041749807171667961/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(417496841922782739/100000000000000000000 : ℝ) ≤ ((64263593821752758241/64270000000000000000 : ℝ)+2*(622721238211/160675000000000 : ℝ)*(13497/50000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (64263593821752758241/64270000000000000000 : ℝ)+2*(622721238211/160675000000000 : ℝ)*(13497/50000 : ℝ)=(10019927138414019/10000000000000000 : ℝ) by norm_num, show 1+2*(417496841922782739/100000000000000000000 : ℝ)=(50417496841922782739/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (64263593821752758241/64270000000000000000 : ℝ)*(X 1 0+X 2 0)+(622721238211/160675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (643/50000 : ℝ)) (hi := (13497/50000 : ℝ)) (c := (64263593821752758241/64270000000000000000 : ℝ)) (alpha := (622721238211/160675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (64263593821752758241/64270000000000000000 : ℝ)*(X 0 1+X 2 1)+(622721238211/160675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (643/50000 : ℝ)) (hi := (13497/50000 : ℝ)) (c := (64263593821752758241/64270000000000000000 : ℝ)) (alpha := (622721238211/160675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (64263593821752758241/64270000000000000000 : ℝ)*(X 0 2+X 1 2)+(622721238211/160675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (643/50000 : ℝ)) (hi := (13497/50000 : ℝ)) (c := (64263593821752758241/64270000000000000000 : ℝ)) (alpha := (622721238211/160675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-250813589/1250000000 : ℝ)*X 0 0+(706230831/1250000000 : ℝ)*X 0 1+(5041368139/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((540749767/1000000000 : ℝ)*X 1 0+(-1165842291/5000000000 : ℝ)*X 1 1+(2520684131/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5407497909/10000000000 : ℝ)*X 2 0+(5041367801/10000000000 : ℝ)*X 2 1+(-2331684857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4295328087/10000000000 : ℝ)*X 0 0+(926430667/2500000000 : ℝ)*X 0 1+(2486038949/5000000000 : ℝ)*X 0 2+(4295328087/10000000000 : ℝ)*X 1 0+(926430667/2500000000 : ℝ)*X 1 1+(2486038949/5000000000 : ℝ)*X 1 2+(4295328087/10000000000 : ℝ)*X 2 0+(926430667/2500000000 : ℝ)*X 2 1+(2486038949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-501769381/2500000000 : ℝ)*X 0 0+(315568937/625000000 : ℝ)*X 0 1+(5641969181/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5249833153/10000000000 : ℝ)*X 1 0+(-432770949/2500000000 : ℝ)*X 1 1+(176311523/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1312458221/2500000000 : ℝ)*X 2 0+(5641968569/10000000000 : ℝ)*X 2 1+(-1731084419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((537063891/1250000000 : ℝ)*X 0 0+(309748721/625000000 : ℝ)*X 0 1+(1861059089/5000000000 : ℝ)*X 0 2+(537063891/1250000000 : ℝ)*X 1 0+(309748721/625000000 : ℝ)*X 1 1+(1861059089/5000000000 : ℝ)*X 1 2+(537063891/1250000000 : ℝ)*X 2 0+(309748721/625000000 : ℝ)*X 2 1+(1861059089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9335199544443345588719240247/1606750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36532947/50000000000000 : ℝ)*(base1) + (864965611/100000000000000 : ℝ)*(base19) + (937602693/100000000000000 : ℝ)*(base23) + (169487659/100000000000000 : ℝ)*(upper3) + (38170067/50000000000000 : ℝ)*(upper5) + (1216562299948611/100000000000000 : ℝ)*(major0) + (1216562299948611/100000000000000 : ℝ)*(major1) + (1216562299948611/100000000000000 : ℝ)*(major2) + (1643448233466019/100000000000000 : ℝ)*(sp0) + (821725668994043/50000000000000 : ℝ)*(sp1) + (410862816337751/25000000000000 : ℝ)*(sp2) + (789669698033533/100000000000000 : ℝ)*(sp3) + (1010638393/25000000000000 : ℝ)*(sp4) + (2432177799/100000000000000 : ℝ)*(sp7) + (394836101638613/50000000000000 : ℝ)*(f.failure) + (1643452202953697/100000000000000 : ℝ)*(f.sum) + (62663846838439/32135000000000000000000000000 : ℝ)*base65 + (33740513205987153251/6427000000000000000000000000000000 : ℝ)*base67 + (577013346392153251/6427000000000000000000000000000000 : ℝ)*base69 + (12635150005474153251/6427000000000000000000000000000000 : ℝ)*base71 + (44911688844531/8033750000000000000000000000 : ℝ)*base73 + (26437553071900846749/6427000000000000000000000000000000 : ℝ)*base76 + (7825883645642153251/6427000000000000000000000000000000 : ℝ)*base77 + (8327638038151153251/6427000000000000000000000000000000 : ℝ)*base79 + (24594106631363/4016875000000000000000000000 : ℝ)*base81 + (1297739/312500000000000000000 : ℝ)*base90 + (1297739/312500000000000000000 : ℝ)*base92 + (1297739/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3434962711702281405357194727/321350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6806299/25000000000000 : ℝ)*(base1) + (1940045991/100000000000000 : ℝ)*(base19) + (55568339/3125000000000 : ℝ)*(base23) + (1449861/800000000000 : ℝ)*(upper3) + (55395511/20000000000000 : ℝ)*(upper5) + (249718553907149/20000000000000 : ℝ)*(major0) + (249718553907149/20000000000000 : ℝ)*(major1) + (624296384767873/50000000000000 : ℝ)*(major2) + (2388551167/25000000000000 : ℝ)*(sp1) + (1408496647/20000000000000 : ℝ)*(sp2) + (843360993200249/50000000000000 : ℝ)*(sp4) + (1686710464924643/100000000000000 : ℝ)*(sp5) + (1686713138505219/100000000000000 : ℝ)*(sp6) + (25326974886423/3125000000000 : ℝ)*(sp7) + (202615805897683/25000000000000 : ℝ)*(f.failure) + (843360979587651/50000000000000 : ℝ)*(f.sum) + (21947877704821/16067500000000000000000000000 : ℝ)*base65 + (4340079605053755091/1285400000000000000000000000000000 : ℝ)*base68 + (4941721555359208607/3213500000000000000000000000000000 : ℝ)*base70 + (9651527521522755091/1285400000000000000000000000000000 : ℝ)*base72 + (4212891976391/16067500000000000000000000000 : ℝ)*base73 + (22468289033739791393/3213500000000000000000000000000000 : ℝ)*base75 + (6308743075808435091/1285400000000000000000000000000000 : ℝ)*base78 + (6304742040792635091/1285400000000000000000000000000000 : ℝ)*base80 + (3279905000481/803375000000000000000000000 : ℝ)*base82 + (1046551/156250000000000000000 : ℝ)*base89 + (1046551/156250000000000000000 : ℝ)*base91 + (515949/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1325_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13497/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (673/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19591/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1325_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1325_s2_0 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2048163619/10000000000 : ℝ)*x 0 + (2742248867/5000000000 : ℝ)*x 1 + (2590030293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2048163619/10000000000 : ℝ)^4285 ≤ (6224341858731/50000000000000 : ℝ)^3261 := by
    have hnat : (2048163619 : ℕ)^4285*50000000000000^3261 ≤ 6224341858731^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048163619 10000000000 6224341858731 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2742248867/5000000000 : ℝ)^4285 ≤ (5677173528889/12500000000000 : ℝ)^3261 := by
    have hnat : (2742248867 : ℕ)^4285*12500000000000^3261 ≤ 5677173528889^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742248867 5000000000 5677173528889 12500000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590030293/5000000000 : ℝ)^4285 ≤ (21066964020111/50000000000000 : ℝ)^3261 := by
    have hnat : (2590030293 : ℕ)^4285*50000000000000^3261 ≤ 21066964020111^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590030293 5000000000 21066964020111 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2048163619/10000000000 : ℝ), (2742248867/5000000000 : ℝ), (2590030293/5000000000 : ℝ)] ![(6224341858731/50000000000000 : ℝ), (5677173528889/12500000000000 : ℝ), (21066964020111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2048163619/10000000000 : ℝ)|^4285 ≤ (6224341858731/50000000000000 : ℝ)^3261
        have hw : |(-2048163619/10000000000 : ℝ)|=(2048163619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2742248867/5000000000 : ℝ)|^4285 ≤ (5677173528889/12500000000000 : ℝ)^3261
        have hw : |(2742248867/5000000000 : ℝ)|=(2742248867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590030293/5000000000 : ℝ)|^4285 ≤ (21066964020111/50000000000000 : ℝ)^3261
        have hw : |(2590030293/5000000000 : ℝ)|=(2590030293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s2_1 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2683582181/5000000000 : ℝ)*x 0 + (-2205619531/10000000000 : ℝ)*x 1 + (2590030051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683582181/5000000000 : ℝ)^4285 ≤ (11036236248061/25000000000000 : ℝ)^3261 := by
    have hnat : (2683582181 : ℕ)^4285*25000000000000^3261 ≤ 11036236248061^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683582181 5000000000 11036236248061 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205619531/10000000000 : ℝ)^4285 ≤ (13721132135781/100000000000000 : ℝ)^3261 := by
    have hnat : (2205619531 : ℕ)^4285*100000000000000^3261 ≤ 13721132135781^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205619531 10000000000 13721132135781 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590030051/5000000000 : ℝ)^4285 ≤ (21066961433611/50000000000000 : ℝ)^3261 := by
    have hnat : (2590030051 : ℕ)^4285*50000000000000^3261 ≤ 21066961433611^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590030051 5000000000 21066961433611 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683582181/5000000000 : ℝ), (-2205619531/10000000000 : ℝ), (2590030051/5000000000 : ℝ)] ![(11036236248061/25000000000000 : ℝ), (13721132135781/100000000000000 : ℝ), (21066961433611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683582181/5000000000 : ℝ)|^4285 ≤ (11036236248061/25000000000000 : ℝ)^3261
        have hw : |(2683582181/5000000000 : ℝ)|=(2683582181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2205619531/10000000000 : ℝ)|^4285 ≤ (13721132135781/100000000000000 : ℝ)^3261
        have hw : |(-2205619531/10000000000 : ℝ)|=(2205619531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590030051/5000000000 : ℝ)|^4285 ≤ (21066961433611/50000000000000 : ℝ)^3261
        have hw : |(2590030051/5000000000 : ℝ)|=(2590030051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s2_2 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2683581849/5000000000 : ℝ)*x 0 + (5180060757/10000000000 : ℝ)*x 1 + (-2205619551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683581849/5000000000 : ℝ)^4285 ≤ (8828987563177/20000000000000 : ℝ)^3261 := by
    have hnat : (2683581849 : ℕ)^4285*20000000000000^3261 ≤ 8828987563177^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683581849 5000000000 8828987563177 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180060757/10000000000 : ℝ)^4285 ≤ (42133929867873/100000000000000 : ℝ)^3261 := by
    have hnat : (5180060757 : ℕ)^4285*100000000000000^3261 ≤ 42133929867873^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180060757 10000000000 42133929867873 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205619551/10000000000 : ℝ)^4285 ≤ (13721132299271/100000000000000 : ℝ)^3261 := by
    have hnat : (2205619551 : ℕ)^4285*100000000000000^3261 ≤ 13721132299271^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205619551 10000000000 13721132299271 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683581849/5000000000 : ℝ), (5180060757/10000000000 : ℝ), (-2205619551/10000000000 : ℝ)] ![(8828987563177/20000000000000 : ℝ), (42133929867873/100000000000000 : ℝ), (13721132299271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683581849/5000000000 : ℝ)|^4285 ≤ (8828987563177/20000000000000 : ℝ)^3261
        have hw : |(2683581849/5000000000 : ℝ)|=(2683581849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180060757/10000000000 : ℝ)|^4285 ≤ (42133929867873/100000000000000 : ℝ)^3261
        have hw : |(5180060757/10000000000 : ℝ)|=(5180060757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2205619551/10000000000 : ℝ)|^4285 ≤ (13721132299271/100000000000000 : ℝ)^3261
        have hw : |(-2205619551/10000000000 : ℝ)|=(2205619551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s2_3 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324401207/10000000000 : ℝ)*x 0 + (502312063/1250000000 : ℝ)*x 1 + (2326047421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324401207/10000000000 : ℝ)^4285 ≤ (16617726473987/50000000000000 : ℝ)^3261 := by
    have hnat : (4324401207 : ℕ)^4285*50000000000000^3261 ≤ 16617726473987^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324401207 10000000000 16617726473987 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502312063/1250000000 : ℝ)^4285 ≤ (30181024542231/100000000000000 : ℝ)^3261 := by
    have hnat : (502312063 : ℕ)^4285*100000000000000^3261 ≤ 30181024542231^3261*1250000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502312063 1250000000 30181024542231 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2326047421/5000000000 : ℝ)^4285 ≤ (36583522492421/100000000000000 : ℝ)^3261 := by
    have hnat : (2326047421 : ℕ)^4285*100000000000000^3261 ≤ 36583522492421^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2326047421 5000000000 36583522492421 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324401207/10000000000 : ℝ), (502312063/1250000000 : ℝ), (2326047421/5000000000 : ℝ)] ![(16617726473987/50000000000000 : ℝ), (30181024542231/100000000000000 : ℝ), (36583522492421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324401207/10000000000 : ℝ)|^4285 ≤ (16617726473987/50000000000000 : ℝ)^3261
        have hw : |(4324401207/10000000000 : ℝ)|=(4324401207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502312063/1250000000 : ℝ)|^4285 ≤ (30181024542231/100000000000000 : ℝ)^3261
        have hw : |(502312063/1250000000 : ℝ)|=(502312063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2326047421/5000000000 : ℝ)|^4285 ≤ (36583522492421/100000000000000 : ℝ)^3261
        have hw : |(2326047421/5000000000 : ℝ)|=(2326047421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s2_4 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2048234467/10000000000 : ℝ)*x 0 + (647750747/1250000000 : ℝ)*x 1 + (5482534697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2048234467/10000000000 : ℝ)^4285 ≤ (6224624775553/50000000000000 : ℝ)^3261 := by
    have hnat : (2048234467 : ℕ)^4285*50000000000000^3261 ≤ 6224624775553^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048234467 10000000000 6224624775553 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647750747/1250000000 : ℝ)^4285 ≤ (4215472162759/10000000000000 : ℝ)^3261 := by
    have hnat : (647750747 : ℕ)^4285*10000000000000^3261 ≤ 4215472162759^3261*1250000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647750747 1250000000 4215472162759 10000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5482534697/10000000000 : ℝ)^4285 ≤ (9079205762779/20000000000000 : ℝ)^3261 := by
    have hnat : (5482534697 : ℕ)^4285*20000000000000^3261 ≤ 9079205762779^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482534697 10000000000 9079205762779 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2048234467/10000000000 : ℝ), (647750747/1250000000 : ℝ), (5482534697/10000000000 : ℝ)] ![(6224624775553/50000000000000 : ℝ), (4215472162759/10000000000000 : ℝ), (9079205762779/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2048234467/10000000000 : ℝ)|^4285 ≤ (6224624775553/50000000000000 : ℝ)^3261
        have hw : |(-2048234467/10000000000 : ℝ)|=(2048234467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647750747/1250000000 : ℝ)|^4285 ≤ (4215472162759/10000000000000 : ℝ)^3261
        have hw : |(647750747/1250000000 : ℝ)|=(647750747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5482534697/10000000000 : ℝ)|^4285 ≤ (9079205762779/20000000000000 : ℝ)^3261
        have hw : |(5482534697/10000000000 : ℝ)|=(5482534697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s2_5 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288841797/10000000000 : ℝ)*x 0 + (-475786099/2500000000 : ℝ)*x 1 + (2741267373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288841797/10000000000 : ℝ)^4285 ≤ (8660079734981/20000000000000 : ℝ)^3261 := by
    have hnat : (5288841797 : ℕ)^4285*20000000000000^3261 ≤ 8660079734981^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288841797 10000000000 8660079734981 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (475786099/2500000000 : ℝ)^4285 ≤ (11303571952319/100000000000000 : ℝ)^3261 := by
    have hnat : (475786099 : ℕ)^4285*100000000000000^3261 ≤ 11303571952319^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475786099 2500000000 11303571952319 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2741267373/5000000000 : ℝ)^4285 ≤ (2837251834189/6250000000000 : ℝ)^3261 := by
    have hnat : (2741267373 : ℕ)^4285*6250000000000^3261 ≤ 2837251834189^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741267373 5000000000 2837251834189 6250000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288841797/10000000000 : ℝ), (-475786099/2500000000 : ℝ), (2741267373/5000000000 : ℝ)] ![(8660079734981/20000000000000 : ℝ), (11303571952319/100000000000000 : ℝ), (2837251834189/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288841797/10000000000 : ℝ)|^4285 ≤ (8660079734981/20000000000000 : ℝ)^3261
        have hw : |(5288841797/10000000000 : ℝ)|=(5288841797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-475786099/2500000000 : ℝ)|^4285 ≤ (11303571952319/100000000000000 : ℝ)^3261
        have hw : |(-475786099/2500000000 : ℝ)|=(475786099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2741267373/5000000000 : ℝ)|^4285 ≤ (2837251834189/6250000000000 : ℝ)^3261
        have hw : |(2741267373/5000000000 : ℝ)|=(2741267373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s2_6 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528884187/1000000000 : ℝ)*x 0 + (342658419/625000000 : ℝ)*x 1 + (-380628871/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528884187/1000000000 : ℝ)^4285 ≤ (43300399460239/100000000000000 : ℝ)^3261 := by
    have hnat : (528884187 : ℕ)^4285*100000000000000^3261 ≤ 43300399460239^3261*1000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528884187 1000000000 43300399460239 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342658419/625000000 : ℝ)^4285 ≤ (5674503611257/12500000000000 : ℝ)^3261 := by
    have hnat : (342658419 : ℕ)^4285*12500000000000^3261 ≤ 5674503611257^3261*625000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342658419 625000000 5674503611257 12500000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (380628871/2000000000 : ℝ)^4285 ≤ (706473227021/6250000000000 : ℝ)^3261 := by
    have hnat : (380628871 : ℕ)^4285*6250000000000^3261 ≤ 706473227021^3261*2000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380628871 2000000000 706473227021 6250000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528884187/1000000000 : ℝ), (342658419/625000000 : ℝ), (-380628871/2000000000 : ℝ)] ![(43300399460239/100000000000000 : ℝ), (5674503611257/12500000000000 : ℝ), (706473227021/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528884187/1000000000 : ℝ)|^4285 ≤ (43300399460239/100000000000000 : ℝ)^3261
        have hw : |(528884187/1000000000 : ℝ)|=(528884187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342658419/625000000 : ℝ)|^4285 ≤ (5674503611257/12500000000000 : ℝ)^3261
        have hw : |(342658419/625000000 : ℝ)|=(342658419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-380628871/2000000000 : ℝ)|^4285 ≤ (706473227021/6250000000000 : ℝ)^3261
        have hw : |(-380628871/2000000000 : ℝ)|=(380628871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s2_7 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540568367/1250000000 : ℝ)*x 0 + (18156421/39062500 : ℝ)*x 1 + (1005646951/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540568367/1250000000 : ℝ)^4285 ≤ (6647384932741/20000000000000 : ℝ)^3261 := by
    have hnat : (540568367 : ℕ)^4285*20000000000000^3261 ≤ 6647384932741^3261*1250000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540568367 1250000000 6647384932741 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18156421/39062500 : ℝ)^4285 ≤ (18270833767127/50000000000000 : ℝ)^3261 := by
    have hnat : (18156421 : ℕ)^4285*50000000000000^3261 ≤ 18270833767127^3261*39062500^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18156421 39062500 18270833767127 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005646951/2500000000 : ℝ)^4285 ≤ (30221407780179/100000000000000 : ℝ)^3261 := by
    have hnat : (1005646951 : ℕ)^4285*100000000000000^3261 ≤ 30221407780179^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005646951 2500000000 30221407780179 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540568367/1250000000 : ℝ), (18156421/39062500 : ℝ), (1005646951/2500000000 : ℝ)] ![(6647384932741/20000000000000 : ℝ), (18270833767127/50000000000000 : ℝ), (30221407780179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540568367/1250000000 : ℝ)|^4285 ≤ (6647384932741/20000000000000 : ℝ)^3261
        have hw : |(540568367/1250000000 : ℝ)|=(540568367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(18156421/39062500 : ℝ)|^4285 ≤ (18270833767127/50000000000000 : ℝ)^3261
        have hw : |(18156421/39062500 : ℝ)|=(18156421/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005646951/2500000000 : ℝ)|^4285 ≤ (30221407780179/100000000000000 : ℝ)^3261
        have hw : |(1005646951/2500000000 : ℝ)|=(1005646951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1325_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19591/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (673/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (4869/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16173/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19591/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (673/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19591/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (673/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19591/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (673/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19591/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (673/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19591/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (673/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19591/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (673/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (673/10000 : ℝ) ^ (1071/256 : ℝ) ≤ (249989140430157/20000000000000000000 : ℝ) := by
    have hpowers : (673/10000 : ℝ)^1071 ≤ (249989140430157/20000000000000000000 : ℝ)^256 := by
      have hnat : (673 : ℕ)^1071*20000000000000000000^256 ≤ 249989140430157^256*10000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        673 10000 249989140430157 20000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (673/10000 : ℝ)) (X := (249989140430157/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hpowhi : (19591/100000 : ℝ) ^ (1071/256 : ℝ) ≤ (109207492576518943/100000000000000000000 : ℝ) := by
    have hpowers : (19591/100000 : ℝ)^1071 ≤ (109207492576518943/100000000000000000000 : ℝ)^256 := by
      have hnat : (19591 : ℕ)^1071*100000000000000000000^256 ≤ 109207492576518943^256*100000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19591 100000 109207492576518943 100000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19591/100000 : ℝ)) (X := (109207492576518943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000249989140430157/10000000000000000000 : ℝ) ≤ (2000011950814423/2000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (10000249989140430157/10000000000000000000 : ℝ)^256 ≤ (2000011950814423/2000000000000000 : ℝ)^1071 := by
      have hnat : (10000249989140430157 : ℕ)^256*2000000000000000^1071 ≤ 2000011950814423^1071*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000249989140430157 10000000000000000000 2000011950814423 2000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000011950814423/2000000000000000 : ℝ)) (X := (10000249989140430157/10000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (3128451794946208429/3125000000000000000 : ℝ) ≤ (1250329892947609/1250000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (3128451794946208429/3125000000000000000 : ℝ)^256 ≤ (1250329892947609/1250000000000000 : ℝ)^1071 := by
      have hnat : (3128451794946208429 : ℕ)^256*1250000000000000^1071 ≤ 1250329892947609^1071*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3128451794946208429 3125000000000000000 1250329892947609 1250000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250329892947609/1250000000000000 : ℝ)) (X := (3128451794946208429/3125000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50109207492576518943/50000000000000000000 : ℝ) ≤ (10005218533089629/10000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (50109207492576518943/50000000000000000000 : ℝ)^256 ≤ (10005218533089629/10000000000000000 : ℝ)^1071 := by
      have hnat : (50109207492576518943 : ℕ)^256*10000000000000000^1071 ≤ 10005218533089629^1071*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50109207492576518943 50000000000000000000 10005218533089629 10000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005218533089629/10000000000000000 : ℝ)) (X := (50109207492576518943/50000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(249989140430157/20000000000000000000 : ℝ) ≤ ((8571736660955573453/8574000000000000000 : ℝ)+2*(859796502919/428700000000000 : ℝ)*(673/10000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (8571736660955573453/8574000000000000000 : ℝ)+2*(859796502919/428700000000000 : ℝ)*(673/10000 : ℝ)=(2000011950814423/2000000000000000 : ℝ) by norm_num, show 1+2*(249989140430157/20000000000000000000 : ℝ)=(10000249989140430157/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(109207492576518943/100000000000000000000 : ℝ)+(249989140430157/20000000000000000000 : ℝ) ≤ ((8571736660955573453/8574000000000000000 : ℝ)+(859796502919/428700000000000 : ℝ)*((19591/100000 : ℝ)+(673/10000 : ℝ)))^(1071/256 : ℝ) := by
    rw [show (8571736660955573453/8574000000000000000 : ℝ)+(859796502919/428700000000000 : ℝ)*((19591/100000 : ℝ)+(673/10000 : ℝ))=(1250329892947609/1250000000000000 : ℝ) by norm_num, show 1+(109207492576518943/100000000000000000000 : ℝ)+(249989140430157/20000000000000000000 : ℝ)=(3128451794946208429/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(109207492576518943/100000000000000000000 : ℝ) ≤ ((8571736660955573453/8574000000000000000 : ℝ)+2*(859796502919/428700000000000 : ℝ)*(19591/100000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (8571736660955573453/8574000000000000000 : ℝ)+2*(859796502919/428700000000000 : ℝ)*(19591/100000 : ℝ)=(10005218533089629/10000000000000000 : ℝ) by norm_num, show 1+2*(109207492576518943/100000000000000000000 : ℝ)=(50109207492576518943/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8571736660955573453/8574000000000000000 : ℝ)*(X 1 0+X 2 0)+(859796502919/428700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (673/10000 : ℝ)) (hi := (19591/100000 : ℝ)) (c := (8571736660955573453/8574000000000000000 : ℝ)) (alpha := (859796502919/428700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8571736660955573453/8574000000000000000 : ℝ)*(X 0 1+X 2 1)+(859796502919/428700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (673/10000 : ℝ)) (hi := (19591/100000 : ℝ)) (c := (8571736660955573453/8574000000000000000 : ℝ)) (alpha := (859796502919/428700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8571736660955573453/8574000000000000000 : ℝ)*(X 0 2+X 1 2)+(859796502919/428700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (673/10000 : ℝ)) (hi := (19591/100000 : ℝ)) (c := (8571736660955573453/8574000000000000000 : ℝ)) (alpha := (859796502919/428700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2048163619/10000000000 : ℝ)*X 0 0+(2742248867/5000000000 : ℝ)*X 0 1+(2590030293/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2683582181/5000000000 : ℝ)*X 1 0+(-2205619531/10000000000 : ℝ)*X 1 1+(2590030051/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2683581849/5000000000 : ℝ)*X 2 0+(5180060757/10000000000 : ℝ)*X 2 1+(-2205619551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324401207/10000000000 : ℝ)*X 0 0+(502312063/1250000000 : ℝ)*X 0 1+(2326047421/5000000000 : ℝ)*X 0 2+(4324401207/10000000000 : ℝ)*X 1 0+(502312063/1250000000 : ℝ)*X 1 1+(2326047421/5000000000 : ℝ)*X 1 2+(4324401207/10000000000 : ℝ)*X 2 0+(502312063/1250000000 : ℝ)*X 2 1+(2326047421/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2048234467/10000000000 : ℝ)*X 0 0+(647750747/1250000000 : ℝ)*X 0 1+(5482534697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288841797/10000000000 : ℝ)*X 1 0+(-475786099/2500000000 : ℝ)*X 1 1+(2741267373/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((528884187/1000000000 : ℝ)*X 2 0+(342658419/625000000 : ℝ)*X 2 1+(-380628871/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((540568367/1250000000 : ℝ)*X 0 0+(18156421/39062500 : ℝ)*X 0 1+(1005646951/2500000000 : ℝ)*X 0 2+(540568367/1250000000 : ℝ)*X 1 0+(18156421/39062500 : ℝ)*X 1 1+(1005646951/2500000000 : ℝ)*X 1 2+(540568367/1250000000 : ℝ)*X 2 0+(18156421/39062500 : ℝ)*X 2 1+(1005646951/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74358687388156073001043089/14290000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (523018693/25000000000000 : ℝ)*(base19) + (1055603041/100000000000000 : ℝ)*(base23) + (338182893/100000000000000 : ℝ)*(lower2) + (373586303/50000000000000 : ℝ)*(upper3) + (25857069/20000000000000 : ℝ)*(upper5) + (243154291600587/10000000000000 : ℝ)*(major0) + (243154291600587/10000000000000 : ℝ)*(major1) + (243154291600587/10000000000000 : ℝ)*(major2) + (1642382272958573/50000000000000 : ℝ)*(sp0) + (656953166608743/20000000000000 : ℝ)*(sp1) + (1642383434757723/50000000000000 : ℝ)*(sp2) + (1578299211715191/100000000000000 : ℝ)*(sp3) + (168960067/5000000000000 : ℝ)*(sp4) + (18521726487/100000000000000 : ℝ)*(sp7) + (789158866720839/50000000000000 : ℝ)*(f.failure) + (1642383962559243/50000000000000 : ℝ)*(f.sum) + (4908674107067/1429000000000000000000000000 : ℝ)*base65 + (16592089857425637/28580000000000000000000000000000 : ℝ)*base67 + (191574033668345637/28580000000000000000000000000000 : ℝ)*base69 + (13151857554405637/28580000000000000000000000000000 : ℝ)*base71 + (3994935168917/1429000000000000000000000000 : ℝ)*base74 + (133616562652174363/28580000000000000000000000000000 : ℝ)*base76 + (143620716626834363/28580000000000000000000000000000 : ℝ)*base78 + (95072837934985637/28580000000000000000000000000000 : ℝ)*base79 + (4083688277303/714500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1433217/312500000000000000000 : ℝ)*base90 + (1433217/312500000000000000000 : ℝ)*base92 + (1433217/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (310011487925627913415588551/71450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56789387/6250000000000 : ℝ)*(base19) + (56040983/5000000000000 : ℝ)*(base23) + (33244853/25000000000000 : ℝ)*(upper3) + (61180961/100000000000000 : ℝ)*(lower4) + (39895873/100000000000000 : ℝ)*(upper5) + (2463150507147533/100000000000000 : ℝ)*(major0) + (2463150507147533/100000000000000 : ℝ)*(major1) + (2463150507147533/100000000000000 : ℝ)*(major2) + (4856534463/50000000000000 : ℝ)*(sp1) + (6564417781/50000000000000 : ℝ)*(sp2) + (3327466606871353/100000000000000 : ℝ)*(sp4) + (1663727992586117/50000000000000 : ℝ)*(sp5) + (332745235721613/10000000000000 : ℝ)*(sp6) + (399708565698767/25000000000000 : ℝ)*(sp7) + (399708565698767/25000000000000 : ℝ)*(f.failure) + (3327466606871353/100000000000000 : ℝ)*(f.sum) + (26123940819967/5358750000000000000000000000 : ℝ)*base66 + (2605911783675381449/857400000000000000000000000000000 : ℝ)*base67 + (167651881939581449/857400000000000000000000000000000 : ℝ)*base69 + (3202363658083418551/857400000000000000000000000000000 : ℝ)*base72 + (46654969747697/21435000000000000000000000000 : ℝ)*base73 + (5474788138174581449/857400000000000000000000000000000 : ℝ)*base75 + (3947227719488181449/857400000000000000000000000000000 : ℝ)*base77 + (8207640004422981449/857400000000000000000000000000000 : ℝ)*base79 + (37760978770273/21435000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (404099/156250000000000000000 : ℝ)*base89 + (404099/156250000000000000000 : ℝ)*base91 + (404099/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1325_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19591/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (673/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4869/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16173/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1325_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1325_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4869/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16173/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1325_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1325_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1325_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4869/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16173/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1325_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
