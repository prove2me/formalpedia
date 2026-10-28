-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1240_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:18:45.578281+00:00
-- url     : https://prove2.me/submissions/8ae29f73-51fa-4821-89bd-f110986b2f0a

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
theorem support_rectangle_w1240_s6_0 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-132554257/625000000 : ℝ)*x 0 + (13478573/25000000 : ℝ)*x 1 + (5267003347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132554257/625000000 : ℝ)^8433 ≤ (2579418014579/20000000000000 : ℝ)^6385 := by
    have hnat : (132554257 : ℕ)^8433*20000000000000^6385 ≤ 2579418014579^6385*625000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132554257 625000000 2579418014579 20000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13478573/25000000 : ℝ)^8433 ≤ (44222924730039/100000000000000 : ℝ)^6385 := by
    have hnat : (13478573 : ℕ)^8433*100000000000000^6385 ≤ 44222924730039^6385*25000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13478573 25000000 44222924730039 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267003347/10000000000 : ℝ)^8433 ≤ (21439992592263/50000000000000 : ℝ)^6385 := by
    have hnat : (5267003347 : ℕ)^8433*50000000000000^6385 ≤ 21439992592263^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267003347 10000000000 21439992592263 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132554257/625000000 : ℝ), (13478573/25000000 : ℝ), (5267003347/10000000000 : ℝ)] ![(2579418014579/20000000000000 : ℝ), (44222924730039/100000000000000 : ℝ), (21439992592263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132554257/625000000 : ℝ)|^8433 ≤ (2579418014579/20000000000000 : ℝ)^6385
        have hw : |(-132554257/625000000 : ℝ)|=(132554257/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13478573/25000000 : ℝ)|^8433 ≤ (44222924730039/100000000000000 : ℝ)^6385
        have hw : |(13478573/25000000 : ℝ)|=(13478573/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267003347/10000000000 : ℝ)|^8433 ≤ (21439992592263/50000000000000 : ℝ)^6385
        have hw : |(5267003347/10000000000 : ℝ)|=(5267003347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s6_1 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672184197/5000000000 : ℝ)*x 0 + (-1091979093/5000000000 : ℝ)*x 1 + (105340069/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672184197/5000000000 : ℝ)^8433 ≤ (21856905672001/50000000000000 : ℝ)^6385 := by
    have hnat : (2672184197 : ℕ)^8433*50000000000000^6385 ≤ 21856905672001^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672184197 5000000000 21856905672001 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091979093/5000000000 : ℝ)^8433 ≤ (418943823461/3125000000000 : ℝ)^6385 := by
    have hnat : (1091979093 : ℕ)^8433*3125000000000^6385 ≤ 418943823461^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091979093 5000000000 418943823461 3125000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105340069/200000000 : ℝ)^8433 ≤ (1071999657301/2500000000000 : ℝ)^6385 := by
    have hnat : (105340069 : ℕ)^8433*2500000000000^6385 ≤ 1071999657301^6385*200000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105340069 200000000 1071999657301 2500000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672184197/5000000000 : ℝ), (-1091979093/5000000000 : ℝ), (105340069/200000000 : ℝ)] ![(21856905672001/50000000000000 : ℝ), (418943823461/3125000000000 : ℝ), (1071999657301/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672184197/5000000000 : ℝ)|^8433 ≤ (21856905672001/50000000000000 : ℝ)^6385
        have hw : |(2672184197/5000000000 : ℝ)|=(2672184197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091979093/5000000000 : ℝ)|^8433 ≤ (418943823461/3125000000000 : ℝ)^6385
        have hw : |(-1091979093/5000000000 : ℝ)|=(1091979093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105340069/200000000 : ℝ)|^8433 ≤ (1071999657301/2500000000000 : ℝ)^6385
        have hw : |(105340069/200000000 : ℝ)|=(105340069/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s6_2 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344368221/10000000000 : ℝ)*x 0 + (5267003451/10000000000 : ℝ)*x 1 + (-1091979207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344368221/10000000000 : ℝ)^8433 ≤ (43713809475087/100000000000000 : ℝ)^6385 := by
    have hnat : (5344368221 : ℕ)^8433*100000000000000^6385 ≤ 43713809475087^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344368221 10000000000 43713809475087 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267003451/10000000000 : ℝ)^8433 ≤ (42879986302793/100000000000000 : ℝ)^6385 := by
    have hnat : (5267003451 : ℕ)^8433*100000000000000^6385 ≤ 42879986302793^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267003451 10000000000 42879986302793 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091979207/5000000000 : ℝ)^8433 ≤ (13406204199243/100000000000000 : ℝ)^6385 := by
    have hnat : (1091979207 : ℕ)^8433*100000000000000^6385 ≤ 13406204199243^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091979207 5000000000 13406204199243 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344368221/10000000000 : ℝ), (5267003451/10000000000 : ℝ), (-1091979207/5000000000 : ℝ)] ![(43713809475087/100000000000000 : ℝ), (42879986302793/100000000000000 : ℝ), (13406204199243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344368221/10000000000 : ℝ)|^8433 ≤ (43713809475087/100000000000000 : ℝ)^6385
        have hw : |(5344368221/10000000000 : ℝ)|=(5344368221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267003451/10000000000 : ℝ)|^8433 ≤ (42879986302793/100000000000000 : ℝ)^6385
        have hw : |(5267003451/10000000000 : ℝ)|=(5267003451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1091979207/5000000000 : ℝ)|^8433 ≤ (13406204199243/100000000000000 : ℝ)^6385
        have hw : |(-1091979207/5000000000 : ℝ)|=(1091979207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s6_3 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (271939851/625000000 : ℝ)*x 0 + (2113331287/5000000000 : ℝ)*x 1 + (4478971477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271939851/625000000 : ℝ)^8433 ≤ (33317380898217/100000000000000 : ℝ)^6385 := by
    have hnat : (271939851 : ℕ)^8433*100000000000000^6385 ≤ 33317380898217^6385*625000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271939851 625000000 33317380898217 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113331287/5000000000 : ℝ)^8433 ≤ (32065324739823/100000000000000 : ℝ)^6385 := by
    have hnat : (2113331287 : ℕ)^8433*100000000000000^6385 ≤ 32065324739823^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113331287 5000000000 32065324739823 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478971477/10000000000 : ℝ)^8433 ≤ (34617294348689/100000000000000 : ℝ)^6385 := by
    have hnat : (4478971477 : ℕ)^8433*100000000000000^6385 ≤ 34617294348689^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478971477 10000000000 34617294348689 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271939851/625000000 : ℝ), (2113331287/5000000000 : ℝ), (4478971477/10000000000 : ℝ)] ![(33317380898217/100000000000000 : ℝ), (32065324739823/100000000000000 : ℝ), (34617294348689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271939851/625000000 : ℝ)|^8433 ≤ (33317380898217/100000000000000 : ℝ)^6385
        have hw : |(271939851/625000000 : ℝ)|=(271939851/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113331287/5000000000 : ℝ)|^8433 ≤ (32065324739823/100000000000000 : ℝ)^6385
        have hw : |(2113331287/5000000000 : ℝ)|=(2113331287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478971477/10000000000 : ℝ)|^8433 ≤ (34617294348689/100000000000000 : ℝ)^6385
        have hw : |(4478971477/10000000000 : ℝ)|=(4478971477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s6_4 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120873083/10000000000 : ℝ)*x 0 + (2633658869/5000000000 : ℝ)*x 1 + (2695556731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120873083/10000000000 : ℝ)^8433 ≤ (1612141249717/12500000000000 : ℝ)^6385 := by
    have hnat : (2120873083 : ℕ)^8433*12500000000000^6385 ≤ 1612141249717^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120873083 10000000000 1612141249717 12500000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633658869/5000000000 : ℝ)^8433 ≤ (5360420715969/12500000000000 : ℝ)^6385 := by
    have hnat : (2633658869 : ℕ)^8433*12500000000000^6385 ≤ 5360420715969^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633658869 5000000000 5360420715969 12500000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695556731/5000000000 : ℝ)^8433 ≤ (44219504246311/100000000000000 : ℝ)^6385 := by
    have hnat : (2695556731 : ℕ)^8433*100000000000000^6385 ≤ 44219504246311^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695556731 5000000000 44219504246311 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120873083/10000000000 : ℝ), (2633658869/5000000000 : ℝ), (2695556731/5000000000 : ℝ)] ![(1612141249717/12500000000000 : ℝ), (5360420715969/12500000000000 : ℝ), (44219504246311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120873083/10000000000 : ℝ)|^8433 ≤ (1612141249717/12500000000000 : ℝ)^6385
        have hw : |(-2120873083/10000000000 : ℝ)|=(2120873083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633658869/5000000000 : ℝ)|^8433 ≤ (5360420715969/12500000000000 : ℝ)^6385
        have hw : |(2633658869/5000000000 : ℝ)|=(2633658869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695556731/5000000000 : ℝ)|^8433 ≤ (44219504246311/100000000000000 : ℝ)^6385
        have hw : |(2695556731/5000000000 : ℝ)|=(2695556731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s6_5 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062524987/2000000000 : ℝ)*x 0 + (-514962187/2500000000 : ℝ)*x 1 + (5391112987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062524987/2000000000 : ℝ)^8433 ≤ (43371214559129/100000000000000 : ℝ)^6385 := by
    have hnat : (1062524987 : ℕ)^8433*100000000000000^6385 ≤ 43371214559129^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062524987 2000000000 43371214559129 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514962187/2500000000 : ℝ)^8433 ≤ (2481857266307/20000000000000 : ℝ)^6385 := by
    have hnat : (514962187 : ℕ)^8433*20000000000000^6385 ≤ 2481857266307^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514962187 2500000000 2481857266307 20000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391112987/10000000000 : ℝ)^8433 ≤ (44219499100543/100000000000000 : ℝ)^6385 := by
    have hnat : (5391112987 : ℕ)^8433*100000000000000^6385 ≤ 44219499100543^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391112987 10000000000 44219499100543 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062524987/2000000000 : ℝ), (-514962187/2500000000 : ℝ), (5391112987/10000000000 : ℝ)] ![(43371214559129/100000000000000 : ℝ), (2481857266307/20000000000000 : ℝ), (44219499100543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062524987/2000000000 : ℝ)|^8433 ≤ (43371214559129/100000000000000 : ℝ)^6385
        have hw : |(1062524987/2000000000 : ℝ)|=(1062524987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514962187/2500000000 : ℝ)|^8433 ≤ (2481857266307/20000000000000 : ℝ)^6385
        have hw : |(-514962187/2500000000 : ℝ)|=(514962187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391112987/10000000000 : ℝ)|^8433 ≤ (44219499100543/100000000000000 : ℝ)^6385
        have hw : |(5391112987/10000000000 : ℝ)|=(5391112987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s6_6 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312624629/10000000000 : ℝ)*x 0 + (53911133/100000000 : ℝ)*x 1 + (-411969747/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312624629/10000000000 : ℝ)^8433 ≤ (43371211259729/100000000000000 : ℝ)^6385 := by
    have hnat : (5312624629 : ℕ)^8433*100000000000000^6385 ≤ 43371211259729^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312624629 10000000000 43371211259729 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53911133/100000000 : ℝ)^8433 ≤ (44219502491333/100000000000000 : ℝ)^6385 := by
    have hnat : (53911133 : ℕ)^8433*100000000000000^6385 ≤ 44219502491333^6385*100000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53911133 100000000 44219502491333 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411969747/2000000000 : ℝ)^8433 ≤ (6204643114049/50000000000000 : ℝ)^6385 := by
    have hnat : (411969747 : ℕ)^8433*50000000000000^6385 ≤ 6204643114049^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411969747 2000000000 6204643114049 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312624629/10000000000 : ℝ), (53911133/100000000 : ℝ), (-411969747/2000000000 : ℝ)] ![(43371211259729/100000000000000 : ℝ), (44219502491333/100000000000000 : ℝ), (6204643114049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312624629/10000000000 : ℝ)|^8433 ≤ (43371211259729/100000000000000 : ℝ)^6385
        have hw : |(5312624629/10000000000 : ℝ)|=(5312624629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53911133/100000000 : ℝ)|^8433 ≤ (44219502491333/100000000000000 : ℝ)^6385
        have hw : |(53911133/100000000 : ℝ)|=(53911133/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411969747/2000000000 : ℝ)|^8433 ≤ (6204643114049/50000000000000 : ℝ)^6385
        have hw : |(-411969747/2000000000 : ℝ)|=(411969747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s6_7 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175523933/5000000000 : ℝ)*x 0 + (4478333221/10000000000 : ℝ)*x 1 + (845460487/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175523933/5000000000 : ℝ)^8433 ≤ (33317484561091/100000000000000 : ℝ)^6385 := by
    have hnat : (2175523933 : ℕ)^8433*100000000000000^6385 ≤ 33317484561091^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175523933 5000000000 33317484561091 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478333221/10000000000 : ℝ)^8433 ≤ (34610779249931/100000000000000 : ℝ)^6385 := by
    have hnat : (4478333221 : ℕ)^8433*100000000000000^6385 ≤ 34610779249931^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478333221 10000000000 34610779249931 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845460487/2000000000 : ℝ)^8433 ≤ (1282869447113/4000000000000 : ℝ)^6385 := by
    have hnat : (845460487 : ℕ)^8433*4000000000000^6385 ≤ 1282869447113^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845460487 2000000000 1282869447113 4000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175523933/5000000000 : ℝ), (4478333221/10000000000 : ℝ), (845460487/2000000000 : ℝ)] ![(33317484561091/100000000000000 : ℝ), (34610779249931/100000000000000 : ℝ), (1282869447113/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175523933/5000000000 : ℝ)|^8433 ≤ (33317484561091/100000000000000 : ℝ)^6385
        have hw : |(2175523933/5000000000 : ℝ)|=(2175523933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478333221/10000000000 : ℝ)|^8433 ≤ (34610779249931/100000000000000 : ℝ)^6385
        have hw : |(4478333221/10000000000 : ℝ)|=(4478333221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(845460487/2000000000 : ℝ)|^8433 ≤ (1282869447113/4000000000000 : ℝ)^6385
        have hw : |(845460487/2000000000 : ℝ)|=(845460487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1240_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (717/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3527/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14129/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11451/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14129/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11451/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14129/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11451/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14129/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11451/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14129/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11451/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14129/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11451/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11451/100000 : ℝ) ^ (527/128 : ℝ) ≤ (266754569119317/2000000000000000000 : ℝ) := by
    have hpowers : (11451/100000 : ℝ)^527 ≤ (266754569119317/2000000000000000000 : ℝ)^128 := by
      have hnat : (11451 : ℕ)^527*2000000000000000000^128 ≤ 266754569119317^128*100000^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11451 100000 266754569119317 2000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11451/100000 : ℝ)) (X := (266754569119317/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14129/100000 : ℝ) ^ (527/128 : ℝ) ≤ (3960585527376383/12500000000000000000 : ℝ) := by
    have hpowers : (14129/100000 : ℝ)^527 ≤ (3960585527376383/12500000000000000000 : ℝ)^128 := by
      have hnat : (14129 : ℕ)^527*12500000000000000000^128 ≤ 3960585527376383^128*100000^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14129 100000 3960585527376383 12500000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14129/100000 : ℝ)) (X := (3960585527376383/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000266754569119317/1000000000000000000 : ℝ) ≤ (10000647839419279/10000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (1000266754569119317/1000000000000000000 : ℝ)^128 ≤ (10000647839419279/10000000000000000 : ℝ)^527 := by
      have hnat : (1000266754569119317 : ℕ)^128*10000000000000000^527 ≤ 10000647839419279^527*1000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000266754569119317 1000000000000000000 10000647839419279 10000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000647839419279/10000000000000000 : ℝ)) (X := (1000266754569119317/1000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022511206337488457/50000000000000000000 : ℝ) ≤ (2000218667433839/2000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (50022511206337488457/50000000000000000000 : ℝ)^128 ≤ (2000218667433839/2000000000000000 : ℝ)^527 := by
      have hnat : (50022511206337488457 : ℕ)^128*2000000000000000^527 ≤ 2000218667433839^527*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022511206337488457 50000000000000000000 2000218667433839 2000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000218667433839/2000000000000000 : ℝ)) (X := (50022511206337488457/50000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253960585527376383/6250000000000000000 : ℝ) ≤ (10001538834919111/10000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (6253960585527376383/6250000000000000000 : ℝ)^128 ≤ (10001538834919111/10000000000000000 : ℝ)^527 := by
      have hnat : (6253960585527376383 : ℕ)^128*10000000000000000^527 ≤ 10001538834919111^527*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253960585527376383 6250000000000000000 10001538834919111 10000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001538834919111/10000000000000000 : ℝ)) (X := (6253960585527376383/6250000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(266754569119317/2000000000000000000 : ℝ) ≤ ((2677153212449625293/2678000000000000000 : ℝ)+2*(111374437479/66950000000000 : ℝ)*(11451/100000 : ℝ))^(527/128 : ℝ) := by
    rw [show (2677153212449625293/2678000000000000000 : ℝ)+2*(111374437479/66950000000000 : ℝ)*(11451/100000 : ℝ)=(10000647839419279/10000000000000000 : ℝ) by norm_num, show 1+2*(266754569119317/2000000000000000000 : ℝ)=(1000266754569119317/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3960585527376383/12500000000000000000 : ℝ)+(266754569119317/2000000000000000000 : ℝ) ≤ ((2677153212449625293/2678000000000000000 : ℝ)+(111374437479/66950000000000 : ℝ)*((14129/100000 : ℝ)+(11451/100000 : ℝ)))^(527/128 : ℝ) := by
    rw [show (2677153212449625293/2678000000000000000 : ℝ)+(111374437479/66950000000000 : ℝ)*((14129/100000 : ℝ)+(11451/100000 : ℝ))=(2000218667433839/2000000000000000 : ℝ) by norm_num, show 1+(3960585527376383/12500000000000000000 : ℝ)+(266754569119317/2000000000000000000 : ℝ)=(50022511206337488457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3960585527376383/12500000000000000000 : ℝ) ≤ ((2677153212449625293/2678000000000000000 : ℝ)+2*(111374437479/66950000000000 : ℝ)*(14129/100000 : ℝ))^(527/128 : ℝ) := by
    rw [show (2677153212449625293/2678000000000000000 : ℝ)+2*(111374437479/66950000000000 : ℝ)*(14129/100000 : ℝ)=(10001538834919111/10000000000000000 : ℝ) by norm_num, show 1+2*(3960585527376383/12500000000000000000 : ℝ)=(6253960585527376383/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2677153212449625293/2678000000000000000 : ℝ)*(X 1 0+X 2 0)+(111374437479/66950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (11451/100000 : ℝ)) (hi := (14129/100000 : ℝ)) (c := (2677153212449625293/2678000000000000000 : ℝ)) (alpha := (111374437479/66950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2677153212449625293/2678000000000000000 : ℝ)*(X 0 1+X 2 1)+(111374437479/66950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (11451/100000 : ℝ)) (hi := (14129/100000 : ℝ)) (c := (2677153212449625293/2678000000000000000 : ℝ)) (alpha := (111374437479/66950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2677153212449625293/2678000000000000000 : ℝ)*(X 0 2+X 1 2)+(111374437479/66950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (11451/100000 : ℝ)) (hi := (14129/100000 : ℝ)) (c := (2677153212449625293/2678000000000000000 : ℝ)) (alpha := (111374437479/66950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-132554257/625000000 : ℝ)*X 0 0+(13478573/25000000 : ℝ)*X 0 1+(5267003347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672184197/5000000000 : ℝ)*X 1 0+(-1091979093/5000000000 : ℝ)*X 1 1+(105340069/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344368221/10000000000 : ℝ)*X 2 0+(5267003451/10000000000 : ℝ)*X 2 1+(-1091979207/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271939851/625000000 : ℝ)*X 0 0+(2113331287/5000000000 : ℝ)*X 0 1+(4478971477/10000000000 : ℝ)*X 0 2+(271939851/625000000 : ℝ)*X 1 0+(2113331287/5000000000 : ℝ)*X 1 1+(4478971477/10000000000 : ℝ)*X 1 2+(271939851/625000000 : ℝ)*X 2 0+(2113331287/5000000000 : ℝ)*X 2 1+(4478971477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2120873083/10000000000 : ℝ)*X 0 0+(2633658869/5000000000 : ℝ)*X 0 1+(2695556731/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062524987/2000000000 : ℝ)*X 1 0+(-514962187/2500000000 : ℝ)*X 1 1+(5391112987/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312624629/10000000000 : ℝ)*X 2 0+(53911133/100000000 : ℝ)*X 2 1+(-411969747/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175523933/5000000000 : ℝ)*X 0 0+(4478333221/10000000000 : ℝ)*X 0 1+(845460487/2000000000 : ℝ)*X 0 2+(2175523933/5000000000 : ℝ)*X 1 0+(4478333221/10000000000 : ℝ)*X 1 1+(845460487/2000000000 : ℝ)*X 1 2+(2175523933/5000000000 : ℝ)*X 2 0+(4478333221/10000000000 : ℝ)*X 2 1+(845460487/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43123738235321670243193323/6695000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (415817027/50000000000000 : ℝ)*(base19) + (70499671/12500000000000 : ℝ)*(base23) + (4183257/12500000000000 : ℝ)*(upper2) + (9242149/10000000000000 : ℝ)*(upper3) + (600020637325237/10000000000000 : ℝ)*(major0) + (600020637325237/10000000000000 : ℝ)*(major1) + (600020637325237/10000000000000 : ℝ)*(major2) + (4018477414647691/50000000000000 : ℝ)*(sp0) + (1607396987127431/20000000000000 : ℝ)*(sp1) + (4018486701057467/50000000000000 : ℝ)*(sp2) + (990852801615523/25000000000000 : ℝ)*(sp3) + (30937975827/100000000000000 : ℝ)*(sp4) + (5900579453/50000000000000 : ℝ)*(sp6) + (7779032621/50000000000000 : ℝ)*(sp7) + (1981713382263667/50000000000000 : ℝ)*(f.failure) + (8036985767271209/100000000000000 : ℝ)*(f.sum) + (14289796955451/1339000000000000000000000000 : ℝ)*base65 + (308795171645140559/26780000000000000000000000000000 : ℝ)*base68 + (138798885418620559/26780000000000000000000000000000 : ℝ)*base70 + (195997337585580559/26780000000000000000000000000000 : ℝ)*base72 + (214431830269/167375000000000000000000000 : ℝ)*base73 + (265127057925780559/26780000000000000000000000000000 : ℝ)*base76 + (157945105956379441/26780000000000000000000000000000 : ℝ)*base77 + (102975160033380559/26780000000000000000000000000000 : ℝ)*base80 + (164062247227/66950000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (16119453/5000000000000000000000 : ℝ)*base89 + (16119453/5000000000000000000000 : ℝ)*base91 + (16119453/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (530704711040285379190971051/66950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1892441827/100000000000000 : ℝ)*(base19) + (45624307/3125000000000 : ℝ)*(base23) + (227241539/100000000000000 : ℝ)*(upper3) + (44304089/100000000000000 : ℝ)*(lower4) + (54609001/12500000000000 : ℝ)*(upper5) + (6030697834412669/100000000000000 : ℝ)*(major0) + (6030697834412669/100000000000000 : ℝ)*(major1) + (6030697834412669/100000000000000 : ℝ)*(major2) + (5262824921/25000000000000 : ℝ)*(sp1) + (12585088699/100000000000000 : ℝ)*(sp2) + (807782755395681/10000000000000 : ℝ)*(sp4) + (4038902305107649/50000000000000 : ℝ)*(sp5) + (8077813508890287/100000000000000 : ℝ)*(sp6) + (3983567850639139/100000000000000 : ℝ)*(sp7) + (3983567850639139/100000000000000 : ℝ)*(f.failure) + (807782755395681/10000000000000 : ℝ)*(f.sum) + (2604832044411/3347500000000000000000000000 : ℝ)*base65 + (2663498512592122983/267800000000000000000000000000000 : ℝ)*base68 + (348888969002922983/267800000000000000000000000000000 : ℝ)*base70 + (1370978650740077017/267800000000000000000000000000000 : ℝ)*base71 + (47354752233843/6695000000000000000000000000 : ℝ)*base74 + (5375015260469722983/267800000000000000000000000000000 : ℝ)*base76 + (1015620102052722983/267800000000000000000000000000000 : ℝ)*base78 + (4233267548770322983/267800000000000000000000000000000 : ℝ)*base80 + (391191390193/1673750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (93521901/10000000000000000000000 : ℝ)*base89 + (93521901/10000000000000000000000 : ℝ)*base91 + (93521901/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1240_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1240_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1240_s7_0 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120882129/10000000000 : ℝ)*x 0 + (5391232857/10000000000 : ℝ)*x 1 + (5267190693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120882129/10000000000 : ℝ)^8433 ≤ (515888106049/4000000000000 : ℝ)^6385 := by
    have hnat : (2120882129 : ℕ)^8433*4000000000000^6385 ≤ 515888106049^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120882129 10000000000 515888106049 4000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391232857/10000000000 : ℝ)^8433 ≤ (44220797680327/100000000000000 : ℝ)^6385 := by
    have hnat : (5391232857 : ℕ)^8433*100000000000000^6385 ≤ 44220797680327^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391232857 10000000000 44220797680327 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267190693/10000000000 : ℝ)^8433 ≤ (5360249955847/12500000000000 : ℝ)^6385 := by
    have hnat : (5267190693 : ℕ)^8433*12500000000000^6385 ≤ 5360249955847^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267190693 10000000000 5360249955847 12500000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120882129/10000000000 : ℝ), (5391232857/10000000000 : ℝ), (5267190693/10000000000 : ℝ)] ![(515888106049/4000000000000 : ℝ), (44220797680327/100000000000000 : ℝ), (5360249955847/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120882129/10000000000 : ℝ)|^8433 ≤ (515888106049/4000000000000 : ℝ)^6385
        have hw : |(-2120882129/10000000000 : ℝ)|=(2120882129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391232857/10000000000 : ℝ)|^8433 ≤ (44220797680327/100000000000000 : ℝ)^6385
        have hw : |(5391232857/10000000000 : ℝ)|=(5391232857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267190693/10000000000 : ℝ)|^8433 ≤ (5360249955847/12500000000000 : ℝ)^6385
        have hw : |(5267190693/10000000000 : ℝ)|=(5267190693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s7_1 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344319287/10000000000 : ℝ)*x 0 + (-109188743/500000000 : ℝ)*x 1 + (1316797753/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344319287/10000000000 : ℝ)^8433 ≤ (43713280842951/100000000000000 : ℝ)^6385 := by
    have hnat : (5344319287 : ℕ)^8433*100000000000000^6385 ≤ 43713280842951^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344319287 10000000000 43713280842951 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109188743/500000000 : ℝ)^8433 ≤ (6702358034979/50000000000000 : ℝ)^6385 := by
    have hnat : (109188743 : ℕ)^8433*50000000000000^6385 ≤ 6702358034979^6385*500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109188743 500000000 6702358034979 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316797753/2500000000 : ℝ)^8433 ≤ (8576400615377/20000000000000 : ℝ)^6385 := by
    have hnat : (1316797753 : ℕ)^8433*20000000000000^6385 ≤ 8576400615377^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316797753 2500000000 8576400615377 20000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344319287/10000000000 : ℝ), (-109188743/500000000 : ℝ), (1316797753/2500000000 : ℝ)] ![(43713280842951/100000000000000 : ℝ), (6702358034979/50000000000000 : ℝ), (8576400615377/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344319287/10000000000 : ℝ)|^8433 ≤ (43713280842951/100000000000000 : ℝ)^6385
        have hw : |(5344319287/10000000000 : ℝ)|=(5344319287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109188743/500000000 : ℝ)|^8433 ≤ (6702358034979/50000000000000 : ℝ)^6385
        have hw : |(-109188743/500000000 : ℝ)|=(109188743/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316797753/2500000000 : ℝ)|^8433 ≤ (8576400615377/20000000000000 : ℝ)^6385
        have hw : |(1316797753/2500000000 : ℝ)|=(1316797753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s7_2 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336079859/2500000000 : ℝ)*x 0 + (5267190957/10000000000 : ℝ)*x 1 + (-2183774733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336079859/2500000000 : ℝ)^8433 ≤ (4371328245259/10000000000000 : ℝ)^6385 := by
    have hnat : (1336079859 : ℕ)^8433*10000000000000^6385 ≤ 4371328245259^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336079859 2500000000 4371328245259 10000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267190957/10000000000 : ℝ)^8433 ≤ (42882002485487/100000000000000 : ℝ)^6385 := by
    have hnat : (5267190957 : ℕ)^8433*100000000000000^6385 ≤ 42882002485487^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267190957 10000000000 42882002485487 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2183774733/10000000000 : ℝ)^8433 ≤ (13404715040343/100000000000000 : ℝ)^6385 := by
    have hnat : (2183774733 : ℕ)^8433*100000000000000^6385 ≤ 13404715040343^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183774733 10000000000 13404715040343 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336079859/2500000000 : ℝ), (5267190957/10000000000 : ℝ), (-2183774733/10000000000 : ℝ)] ![(4371328245259/10000000000000 : ℝ), (42882002485487/100000000000000 : ℝ), (13404715040343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336079859/2500000000 : ℝ)|^8433 ≤ (4371328245259/10000000000000 : ℝ)^6385
        have hw : |(1336079859/2500000000 : ℝ)|=(1336079859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267190957/10000000000 : ℝ)|^8433 ≤ (42882002485487/100000000000000 : ℝ)^6385
        have hw : |(5267190957/10000000000 : ℝ)|=(5267190957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2183774733/10000000000 : ℝ)|^8433 ≤ (13404715040343/100000000000000 : ℝ)^6385
        have hw : |(-2183774733/10000000000 : ℝ)|=(2183774733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s7_3 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087762011/2500000000 : ℝ)*x 0 + (4227050199/10000000000 : ℝ)*x 1 + (1119645163/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087762011/2500000000 : ℝ)^8433 ≤ (16658743180643/50000000000000 : ℝ)^6385 := by
    have hnat : (1087762011 : ℕ)^8433*50000000000000^6385 ≤ 16658743180643^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087762011 2500000000 16658743180643 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227050199/10000000000 : ℝ)^8433 ≤ (32069208723801/100000000000000 : ℝ)^6385 := by
    have hnat : (4227050199 : ℕ)^8433*100000000000000^6385 ≤ 32069208723801^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227050199 10000000000 32069208723801 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119645163/2500000000 : ℝ)^8433 ≤ (3461330490553/10000000000000 : ℝ)^6385 := by
    have hnat : (1119645163 : ℕ)^8433*10000000000000^6385 ≤ 3461330490553^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119645163 2500000000 3461330490553 10000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087762011/2500000000 : ℝ), (4227050199/10000000000 : ℝ), (1119645163/2500000000 : ℝ)] ![(16658743180643/50000000000000 : ℝ), (32069208723801/100000000000000 : ℝ), (3461330490553/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087762011/2500000000 : ℝ)|^8433 ≤ (16658743180643/50000000000000 : ℝ)^6385
        have hw : |(1087762011/2500000000 : ℝ)|=(1087762011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227050199/10000000000 : ℝ)|^8433 ≤ (32069208723801/100000000000000 : ℝ)^6385
        have hw : |(4227050199/10000000000 : ℝ)|=(4227050199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119645163/2500000000 : ℝ)|^8433 ≤ (3461330490553/10000000000000 : ℝ)^6385
        have hw : |(1119645163/2500000000 : ℝ)|=(1119645163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s7_4 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-424177361/2000000000 : ℝ)*x 0 + (1053500731/2000000000 : ℝ)*x 1 + (5390918751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424177361/2000000000 : ℝ)^8433 ≤ (6448620103419/50000000000000 : ℝ)^6385 := by
    have hnat : (424177361 : ℕ)^8433*50000000000000^6385 ≤ 6448620103419^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424177361 2000000000 6448620103419 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053500731/2000000000 : ℝ)^8433 ≤ (1072134121567/2500000000000 : ℝ)^6385 := by
    have hnat : (1053500731 : ℕ)^8433*2500000000000^6385 ≤ 1072134121567^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053500731 2000000000 1072134121567 2500000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390918751/10000000000 : ℝ)^8433 ≤ (22108697458063/50000000000000 : ℝ)^6385 := by
    have hnat : (5390918751 : ℕ)^8433*50000000000000^6385 ≤ 22108697458063^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390918751 10000000000 22108697458063 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-424177361/2000000000 : ℝ), (1053500731/2000000000 : ℝ), (5390918751/10000000000 : ℝ)] ![(6448620103419/50000000000000 : ℝ), (1072134121567/2500000000000 : ℝ), (22108697458063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-424177361/2000000000 : ℝ)|^8433 ≤ (6448620103419/50000000000000 : ℝ)^6385
        have hw : |(-424177361/2000000000 : ℝ)|=(424177361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053500731/2000000000 : ℝ)|^8433 ≤ (1072134121567/2500000000000 : ℝ)^6385
        have hw : |(1053500731/2000000000 : ℝ)|=(1053500731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390918751/10000000000 : ℝ)|^8433 ≤ (22108697458063/50000000000000 : ℝ)^6385
        have hw : |(5390918751/10000000000 : ℝ)|=(5390918751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s7_5 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312673713/10000000000 : ℝ)*x 0 + (-1030023557/5000000000 : ℝ)*x 1 + (269545937/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312673713/10000000000 : ℝ)^8433 ≤ (2710733781351/6250000000000 : ℝ)^6385 := by
    have hnat : (5312673713 : ℕ)^8433*6250000000000^6385 ≤ 2710733781351^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312673713 10000000000 2710733781351 6250000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030023557/5000000000 : ℝ)^8433 ≤ (3102716173383/25000000000000 : ℝ)^6385 := by
    have hnat : (1030023557 : ℕ)^8433*25000000000000^6385 ≤ 3102716173383^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030023557 5000000000 3102716173383 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269545937/500000000 : ℝ)^8433 ≤ (22108697398481/50000000000000 : ℝ)^6385 := by
    have hnat : (269545937 : ℕ)^8433*50000000000000^6385 ≤ 22108697398481^6385*500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269545937 500000000 22108697398481 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312673713/10000000000 : ℝ), (-1030023557/5000000000 : ℝ), (269545937/500000000 : ℝ)] ![(2710733781351/6250000000000 : ℝ), (3102716173383/25000000000000 : ℝ), (22108697398481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312673713/10000000000 : ℝ)|^8433 ≤ (2710733781351/6250000000000 : ℝ)^6385
        have hw : |(5312673713/10000000000 : ℝ)|=(5312673713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030023557/5000000000 : ℝ)|^8433 ≤ (3102716173383/25000000000000 : ℝ)^6385
        have hw : |(-1030023557/5000000000 : ℝ)|=(1030023557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269545937/500000000 : ℝ)|^8433 ≤ (22108697398481/50000000000000 : ℝ)^6385
        have hw : |(269545937/500000000 : ℝ)|=(269545937/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s7_6 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656336849/5000000000 : ℝ)*x 0 + (269545939/500000000 : ℝ)*x 1 + (-1030023539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656336849/5000000000 : ℝ)^8433 ≤ (1084293508497/2500000000000 : ℝ)^6385 := by
    have hnat : (2656336849 : ℕ)^8433*2500000000000^6385 ≤ 1084293508497^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656336849 5000000000 1084293508497 2500000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269545939/500000000 : ℝ)^8433 ≤ (8843479046057/20000000000000 : ℝ)^6385 := by
    have hnat : (269545939 : ℕ)^8433*20000000000000^6385 ≤ 8843479046057^6385*500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269545939 500000000 8843479046057 20000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030023539/5000000000 : ℝ)^8433 ≤ (6205432203541/50000000000000 : ℝ)^6385 := by
    have hnat : (1030023539 : ℕ)^8433*50000000000000^6385 ≤ 6205432203541^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030023539 5000000000 6205432203541 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656336849/5000000000 : ℝ), (269545939/500000000 : ℝ), (-1030023539/5000000000 : ℝ)] ![(1084293508497/2500000000000 : ℝ), (8843479046057/20000000000000 : ℝ), (6205432203541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656336849/5000000000 : ℝ)|^8433 ≤ (1084293508497/2500000000000 : ℝ)^6385
        have hw : |(2656336849/5000000000 : ℝ)|=(2656336849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269545939/500000000 : ℝ)|^8433 ≤ (8843479046057/20000000000000 : ℝ)^6385
        have hw : |(269545939/500000000 : ℝ)|=(269545939/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030023539/5000000000 : ℝ)|^8433 ≤ (6205432203541/50000000000000 : ℝ)^6385
        have hw : |(-1030023539/5000000000 : ℝ)|=(1030023539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s7_7 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4351057081/10000000000 : ℝ)*x 0 + (4477946529/10000000000 : ℝ)*x 1 + (1056921759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351057081/10000000000 : ℝ)^8433 ≤ (3331757775661/10000000000000 : ℝ)^6385 := by
    have hnat : (4351057081 : ℕ)^8433*10000000000000^6385 ≤ 3331757775661^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351057081 10000000000 3331757775661 10000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477946529/10000000000 : ℝ)^8433 ≤ (6921366435049/20000000000000 : ℝ)^6385 := by
    have hnat : (4477946529 : ℕ)^8433*20000000000000^6385 ≤ 6921366435049^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477946529 10000000000 6921366435049 20000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056921759/2500000000 : ℝ)^8433 ≤ (32075590048133/100000000000000 : ℝ)^6385 := by
    have hnat : (1056921759 : ℕ)^8433*100000000000000^6385 ≤ 32075590048133^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056921759 2500000000 32075590048133 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351057081/10000000000 : ℝ), (4477946529/10000000000 : ℝ), (1056921759/2500000000 : ℝ)] ![(3331757775661/10000000000000 : ℝ), (6921366435049/20000000000000 : ℝ), (32075590048133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351057081/10000000000 : ℝ)|^8433 ≤ (3331757775661/10000000000000 : ℝ)^6385
        have hw : |(4351057081/10000000000 : ℝ)|=(4351057081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477946529/10000000000 : ℝ)|^8433 ≤ (6921366435049/20000000000000 : ℝ)^6385
        have hw : |(4477946529/10000000000 : ℝ)|=(4477946529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056921759/2500000000 : ℝ)|^8433 ≤ (32075590048133/100000000000000 : ℝ)^6385
        have hw : |(1056921759/2500000000 : ℝ)|=(1056921759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1240_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (2869/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1763/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3527/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (717/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3527/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (717/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3527/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (717/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3527/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (717/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3527/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (717/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3527/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (717/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (717/6250 : ℝ) ^ (527/128 : ℝ) ≤ (13438723386747821/100000000000000000000 : ℝ) := by
    have hpowers : (717/6250 : ℝ)^527 ≤ (13438723386747821/100000000000000000000 : ℝ)^128 := by
      have hnat : (717 : ℕ)^527*100000000000000000000^128 ≤ 13438723386747821^128*6250^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        717 6250 13438723386747821 100000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (717/6250 : ℝ)) (X := (13438723386747821/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hpowhi : (3527/25000 : ℝ) ^ (527/128 : ℝ) ≤ (31491241794995069/100000000000000000000 : ℝ) := by
    have hpowers : (3527/25000 : ℝ)^527 ≤ (31491241794995069/100000000000000000000 : ℝ)^128 := by
      have hnat : (3527 : ℕ)^527*100000000000000000000^128 ≤ 31491241794995069^128*25000^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3527 25000 31491241794995069 100000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3527/25000 : ℝ)) (X := (31491241794995069/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013438723386747821/50000000000000000000 : ℝ) ≤ (2000130548888107/2000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (50013438723386747821/50000000000000000000 : ℝ)^128 ≤ (2000130548888107/2000000000000000 : ℝ)^527 := by
      have hnat : (50013438723386747821 : ℕ)^128*2000000000000000^527 ≤ 2000130548888107^527*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013438723386747821 50000000000000000000 2000130548888107 2000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000130548888107/2000000000000000 : ℝ)) (X := (50013438723386747821/50000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004492996518174289/10000000000000000000 : ℝ) ≤ (10001091092529491/10000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (10004492996518174289/10000000000000000000 : ℝ)^128 ≤ (10001091092529491/10000000000000000 : ℝ)^527 := by
      have hnat : (10004492996518174289 : ℕ)^128*10000000000000000^527 ≤ 10001091092529491^527*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004492996518174289 10000000000000000000 10001091092529491 10000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001091092529491/10000000000000000 : ℝ)) (X := (10004492996518174289/10000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031491241794995069/50000000000000000000 : ℝ) ≤ (10001529440618447/10000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (50031491241794995069/50000000000000000000 : ℝ)^128 ≤ (10001529440618447/10000000000000000 : ℝ)^527 := by
      have hnat : (50031491241794995069 : ℕ)^128*10000000000000000^527 ≤ 10001529440618447^527*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031491241794995069 50000000000000000000 10001529440618447 10000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001529440618447/10000000000000000 : ℝ)) (X := (50031491241794995069/50000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13438723386747821/100000000000000000000 : ℝ) ≤ ((6587915793948060949/6590000000000000000 : ℝ)+2*(109587022239/65900000000000 : ℝ)*(717/6250 : ℝ))^(527/128 : ℝ) := by
    rw [show (6587915793948060949/6590000000000000000 : ℝ)+2*(109587022239/65900000000000 : ℝ)*(717/6250 : ℝ)=(2000130548888107/2000000000000000 : ℝ) by norm_num, show 1+2*(13438723386747821/100000000000000000000 : ℝ)=(50013438723386747821/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31491241794995069/100000000000000000000 : ℝ)+(13438723386747821/100000000000000000000 : ℝ) ≤ ((6587915793948060949/6590000000000000000 : ℝ)+(109587022239/65900000000000 : ℝ)*((3527/25000 : ℝ)+(717/6250 : ℝ)))^(527/128 : ℝ) := by
    rw [show (6587915793948060949/6590000000000000000 : ℝ)+(109587022239/65900000000000 : ℝ)*((3527/25000 : ℝ)+(717/6250 : ℝ))=(10001091092529491/10000000000000000 : ℝ) by norm_num, show 1+(31491241794995069/100000000000000000000 : ℝ)+(13438723386747821/100000000000000000000 : ℝ)=(10004492996518174289/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31491241794995069/100000000000000000000 : ℝ) ≤ ((6587915793948060949/6590000000000000000 : ℝ)+2*(109587022239/65900000000000 : ℝ)*(3527/25000 : ℝ))^(527/128 : ℝ) := by
    rw [show (6587915793948060949/6590000000000000000 : ℝ)+2*(109587022239/65900000000000 : ℝ)*(3527/25000 : ℝ)=(10001529440618447/10000000000000000 : ℝ) by norm_num, show 1+2*(31491241794995069/100000000000000000000 : ℝ)=(50031491241794995069/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6587915793948060949/6590000000000000000 : ℝ)*(X 1 0+X 2 0)+(109587022239/65900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (717/6250 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (6587915793948060949/6590000000000000000 : ℝ)) (alpha := (109587022239/65900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6587915793948060949/6590000000000000000 : ℝ)*(X 0 1+X 2 1)+(109587022239/65900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (717/6250 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (6587915793948060949/6590000000000000000 : ℝ)) (alpha := (109587022239/65900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6587915793948060949/6590000000000000000 : ℝ)*(X 0 2+X 1 2)+(109587022239/65900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (717/6250 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (6587915793948060949/6590000000000000000 : ℝ)) (alpha := (109587022239/65900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2120882129/10000000000 : ℝ)*X 0 0+(5391232857/10000000000 : ℝ)*X 0 1+(5267190693/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344319287/10000000000 : ℝ)*X 1 0+(-109188743/500000000 : ℝ)*X 1 1+(1316797753/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336079859/2500000000 : ℝ)*X 2 0+(5267190957/10000000000 : ℝ)*X 2 1+(-2183774733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087762011/2500000000 : ℝ)*X 0 0+(4227050199/10000000000 : ℝ)*X 0 1+(1119645163/2500000000 : ℝ)*X 0 2+(1087762011/2500000000 : ℝ)*X 1 0+(4227050199/10000000000 : ℝ)*X 1 1+(1119645163/2500000000 : ℝ)*X 1 2+(1087762011/2500000000 : ℝ)*X 2 0+(4227050199/10000000000 : ℝ)*X 2 1+(1119645163/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-424177361/2000000000 : ℝ)*X 0 0+(1053500731/2000000000 : ℝ)*X 0 1+(5390918751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312673713/10000000000 : ℝ)*X 1 0+(-1030023557/5000000000 : ℝ)*X 1 1+(269545937/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656336849/5000000000 : ℝ)*X 2 0+(269545939/500000000 : ℝ)*X 2 1+(-1030023539/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351057081/10000000000 : ℝ)*X 0 0+(4477946529/10000000000 : ℝ)*X 0 1+(1056921759/2500000000 : ℝ)*X 0 2+(4351057081/10000000000 : ℝ)*X 1 0+(4477946529/10000000000 : ℝ)*X 1 1+(1056921759/2500000000 : ℝ)*X 1 2+(4351057081/10000000000 : ℝ)*X 2 0+(4477946529/10000000000 : ℝ)*X 2 1+(1056921759/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (180078060981497323073522127/41187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1286277467/100000000000000 : ℝ)*(base19) + (270143127/25000000000000 : ℝ)*(base23) + (46011453/20000000000000 : ℝ)*(lower2) + (47158627/25000000000000 : ℝ)*(upper3) + (121294271/100000000000000 : ℝ)*(upper5) + (1504697569676759/25000000000000 : ℝ)*(major0) + (1504697569676759/25000000000000 : ℝ)*(major1) + (1504697569676759/25000000000000 : ℝ)*(major2) + (8061823336170887/100000000000000 : ℝ)*(sp0) + (2015469197929399/25000000000000 : ℝ)*(sp1) + (4030938498711277/50000000000000 : ℝ)*(sp2) + (993919875338821/25000000000000 : ℝ)*(sp3) + (2189672967/4000000000000 : ℝ)*(sp4) + (22832325273/100000000000000 : ℝ)*(sp7) + (1987851166840279/50000000000000 : ℝ)*(f.failure) + (8061878077995063/100000000000000 : ℝ)*(f.sum) + (21476779263859/3295000000000000000000000000 : ℝ)*base65 + (390954305475134291/164750000000000000000000000000000 : ℝ)*base67 + (1495856211148884291/164750000000000000000000000000000 : ℝ)*base69 + (143712814298865709/164750000000000000000000000000000 : ℝ)*base72 + (1036216904569/3295000000000000000000000000 : ℝ)*base73 + (2735289071967884291/164750000000000000000000000000000 : ℝ)*base75 + (336222800894134291/164750000000000000000000000000000 : ℝ)*base77 + (1544937378063634291/164750000000000000000000000000000 : ℝ)*base79 + (9280657573487/1647500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (93191161/5000000000000000000000 : ℝ)*base89 + (93191161/5000000000000000000000 : ℝ)*base91 + (93191161/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3284035264510990017893788443/329500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1577289937/100000000000000 : ℝ)*(base19) + (1766516469/100000000000000 : ℝ)*(base23) + (175781613/100000000000000 : ℝ)*(upper3) + (92834551/100000000000000 : ℝ)*(lower4) + (5032561/2500000000000 : ℝ)*(upper5) + (6049293245176069/100000000000000 : ℝ)*(major0) + (6049293245176069/100000000000000 : ℝ)*(major1) + (6049293245176069/100000000000000 : ℝ)*(major2) + (8765878661/20000000000000 : ℝ)*(sp1) + (25050776591/50000000000000 : ℝ)*(sp2) + (8102735138522303/100000000000000 : ℝ)*(sp4) + (8102689731839061/100000000000000 : ℝ)*(sp5) + (8102683270452653/100000000000000 : ℝ)*(sp6) + (998962754901431/25000000000000 : ℝ)*(sp7) + (998962754901431/25000000000000 : ℝ)*(f.failure) + (8102735138522303/100000000000000 : ℝ)*(f.sum) + (5480868602141/823750000000000000000000000 : ℝ)*base66 + (2420875204301670519/659000000000000000000000000000000 : ℝ)*base68 + (6837845360894329481/659000000000000000000000000000000 : ℝ)*base69 + (403362075649329481/659000000000000000000000000000000 : ℝ)*base71 + (12335288051399/3295000000000000000000000000 : ℝ)*base74 + (6634404167878670519/659000000000000000000000000000000 : ℝ)*base76 + (5235166553112670519/659000000000000000000000000000000 : ℝ)*base78 + (6171890715592670519/659000000000000000000000000000000 : ℝ)*base80 + (7331426937911/3295000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (22272729/2500000000000000000000 : ℝ)*base89 + (22272729/2500000000000000000000 : ℝ)*base91 + (22272729/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1240_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2869/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1240_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1240_s8_0 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1325553/6250000 : ℝ)*x 0 + (2695597743/5000000000 : ℝ)*x 1 + (5267226349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325553/6250000 : ℝ)^8433 ≤ (644861205177/5000000000000 : ℝ)^6385 := by
    have hnat : (1325553 : ℕ)^8433*5000000000000^6385 ≤ 644861205177^6385*6250000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325553 6250000 644861205177 5000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695597743/5000000000 : ℝ)^8433 ≤ (22110196415269/50000000000000 : ℝ)^6385 := by
    have hnat : (2695597743 : ℕ)^8433*50000000000000^6385 ≤ 22110196415269^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695597743 5000000000 22110196415269 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267226349/10000000000 : ℝ)^8433 ≤ (1072059576129/2500000000000 : ℝ)^6385 := by
    have hnat : (5267226349 : ℕ)^8433*2500000000000^6385 ≤ 1072059576129^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267226349 10000000000 1072059576129 2500000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1325553/6250000 : ℝ), (2695597743/5000000000 : ℝ), (5267226349/10000000000 : ℝ)] ![(644861205177/5000000000000 : ℝ), (22110196415269/50000000000000 : ℝ), (1072059576129/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1325553/6250000 : ℝ)|^8433 ≤ (644861205177/5000000000000 : ℝ)^6385
        have hw : |(-1325553/6250000 : ℝ)|=(1325553/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695597743/5000000000 : ℝ)|^8433 ≤ (22110196415269/50000000000000 : ℝ)^6385
        have hw : |(2695597743/5000000000 : ℝ)|=(2695597743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267226349/10000000000 : ℝ)|^8433 ≤ (1072059576129/2500000000000 : ℝ)^6385
        have hw : |(5267226349/10000000000 : ℝ)|=(5267226349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s8_1 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672155047/5000000000 : ℝ)*x 0 + (-1091870149/5000000000 : ℝ)*x 1 + (2633613153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672155047/5000000000 : ℝ)^8433 ≤ (5464147691437/12500000000000 : ℝ)^6385 := by
    have hnat : (2672155047 : ℕ)^8433*12500000000000^6385 ≤ 5464147691437^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672155047 5000000000 5464147691437 12500000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091870149/5000000000 : ℝ)^8433 ≤ (6702217934789/50000000000000 : ℝ)^6385 := by
    have hnat : (1091870149 : ℕ)^8433*50000000000000^6385 ≤ 6702217934789^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091870149 5000000000 6702217934789 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633613153/5000000000 : ℝ)^8433 ≤ (21441191291397/50000000000000 : ℝ)^6385 := by
    have hnat : (2633613153 : ℕ)^8433*50000000000000^6385 ≤ 21441191291397^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633613153 5000000000 21441191291397 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672155047/5000000000 : ℝ), (-1091870149/5000000000 : ℝ), (2633613153/5000000000 : ℝ)] ![(5464147691437/12500000000000 : ℝ), (6702217934789/50000000000000 : ℝ), (21441191291397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672155047/5000000000 : ℝ)|^8433 ≤ (5464147691437/12500000000000 : ℝ)^6385
        have hw : |(2672155047/5000000000 : ℝ)|=(2672155047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091870149/5000000000 : ℝ)|^8433 ≤ (6702217934789/50000000000000 : ℝ)^6385
        have hw : |(-1091870149/5000000000 : ℝ)|=(1091870149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633613153/5000000000 : ℝ)|^8433 ≤ (21441191291397/50000000000000 : ℝ)^6385
        have hw : |(2633613153/5000000000 : ℝ)|=(2633613153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s8_2 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068862019/2000000000 : ℝ)*x 0 + (1316806581/2500000000 : ℝ)*x 1 + (-2183740273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068862019/2000000000 : ℝ)^8433 ≤ (43713181542299/100000000000000 : ℝ)^6385 := by
    have hnat : (1068862019 : ℕ)^8433*100000000000000^6385 ≤ 43713181542299^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068862019 2000000000 43713181542299 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316806581/2500000000 : ℝ)^8433 ≤ (21441191388171/50000000000000 : ℝ)^6385 := by
    have hnat : (1316806581 : ℕ)^8433*50000000000000^6385 ≤ 21441191388171^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316806581 2500000000 21441191388171 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2183740273/10000000000 : ℝ)^8433 ≤ (13404435666899/100000000000000 : ℝ)^6385 := by
    have hnat : (2183740273 : ℕ)^8433*100000000000000^6385 ≤ 13404435666899^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183740273 10000000000 13404435666899 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068862019/2000000000 : ℝ), (1316806581/2500000000 : ℝ), (-2183740273/10000000000 : ℝ)] ![(43713181542299/100000000000000 : ℝ), (21441191388171/50000000000000 : ℝ), (13404435666899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068862019/2000000000 : ℝ)|^8433 ≤ (43713181542299/100000000000000 : ℝ)^6385
        have hw : |(1068862019/2000000000 : ℝ)|=(1068862019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316806581/2500000000 : ℝ)|^8433 ≤ (21441191388171/50000000000000 : ℝ)^6385
        have hw : |(1316806581/2500000000 : ℝ)|=(1316806581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2183740273/10000000000 : ℝ)|^8433 ≤ (13404435666899/100000000000000 : ℝ)^6385
        have hw : |(-2183740273/10000000000 : ℝ)|=(2183740273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s8_3 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087762371/2500000000 : ℝ)*x 0 + (264195237/625000000 : ℝ)*x 1 + (4478506983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087762371/2500000000 : ℝ)^8433 ≤ (16658750462331/50000000000000 : ℝ)^6385 := by
    have hnat : (1087762371 : ℕ)^8433*50000000000000^6385 ≤ 16658750462331^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087762371 2500000000 16658750462331 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264195237/625000000 : ℝ)^8433 ≤ (4008743266881/12500000000000 : ℝ)^6385 := by
    have hnat : (264195237 : ℕ)^8433*12500000000000^6385 ≤ 4008743266881^6385*625000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264195237 625000000 4008743266881 12500000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478506983/10000000000 : ℝ)^8433 ≤ (17306276461721/50000000000000 : ℝ)^6385 := by
    have hnat : (4478506983 : ℕ)^8433*50000000000000^6385 ≤ 17306276461721^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478506983 10000000000 17306276461721 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087762371/2500000000 : ℝ), (264195237/625000000 : ℝ), (4478506983/10000000000 : ℝ)] ![(16658750462331/50000000000000 : ℝ), (4008743266881/12500000000000 : ℝ), (17306276461721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087762371/2500000000 : ℝ)|^8433 ≤ (16658750462331/50000000000000 : ℝ)^6385
        have hw : |(1087762371/2500000000 : ℝ)|=(1087762371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264195237/625000000 : ℝ)|^8433 ≤ (4008743266881/12500000000000 : ℝ)^6385
        have hw : |(264195237/625000000 : ℝ)|=(264195237/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478506983/10000000000 : ℝ)|^8433 ≤ (17306276461721/50000000000000 : ℝ)^6385
        have hw : |(4478506983/10000000000 : ℝ)|=(4478506983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s8_4 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120889479/10000000000 : ℝ)*x 0 + (526753881/1000000000 : ℝ)*x 1 + (2695440937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120889479/10000000000 : ℝ)^8433 ≤ (6448630841631/50000000000000 : ℝ)^6385 := by
    have hnat : (2120889479 : ℕ)^8433*50000000000000^6385 ≤ 6448630841631^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120889479 10000000000 6448630841631 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526753881/1000000000 : ℝ)^8433 ≤ (21442871440579/50000000000000 : ℝ)^6385 := by
    have hnat : (526753881 : ℕ)^8433*50000000000000^6385 ≤ 21442871440579^6385*1000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526753881 1000000000 21442871440579 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695440937/5000000000 : ℝ)^8433 ≤ (11054248856357/25000000000000 : ℝ)^6385 := by
    have hnat : (2695440937 : ℕ)^8433*25000000000000^6385 ≤ 11054248856357^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695440937 5000000000 11054248856357 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120889479/10000000000 : ℝ), (526753881/1000000000 : ℝ), (2695440937/5000000000 : ℝ)] ![(6448630841631/50000000000000 : ℝ), (21442871440579/50000000000000 : ℝ), (11054248856357/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120889479/10000000000 : ℝ)|^8433 ≤ (6448630841631/50000000000000 : ℝ)^6385
        have hw : |(-2120889479/10000000000 : ℝ)|=(2120889479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526753881/1000000000 : ℝ)|^8433 ≤ (21442871440579/50000000000000 : ℝ)^6385
        have hw : |(526753881/1000000000 : ℝ)|=(526753881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695440937/5000000000 : ℝ)|^8433 ≤ (11054248856357/25000000000000 : ℝ)^6385
        have hw : |(2695440937/5000000000 : ℝ)|=(2695440937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s8_5 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312682897/10000000000 : ℝ)*x 0 + (-2060084613/10000000000 : ℝ)*x 1 + (1078176411/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312682897/10000000000 : ℝ)^8433 ≤ (43371839527083/100000000000000 : ℝ)^6385 := by
    have hnat : (5312682897 : ℕ)^8433*100000000000000^6385 ≤ 43371839527083^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312682897 10000000000 43371839527083 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2060084613/10000000000 : ℝ)^8433 ≤ (12411163071699/100000000000000 : ℝ)^6385 := by
    have hnat : (2060084613 : ℕ)^8433*100000000000000^6385 ≤ 12411163071699^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060084613 10000000000 12411163071699 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078176411/2000000000 : ℝ)^8433 ≤ (44216997386209/100000000000000 : ℝ)^6385 := by
    have hnat : (1078176411 : ℕ)^8433*100000000000000^6385 ≤ 44216997386209^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078176411 2000000000 44216997386209 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312682897/10000000000 : ℝ), (-2060084613/10000000000 : ℝ), (1078176411/2000000000 : ℝ)] ![(43371839527083/100000000000000 : ℝ), (12411163071699/100000000000000 : ℝ), (44216997386209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312682897/10000000000 : ℝ)|^8433 ≤ (43371839527083/100000000000000 : ℝ)^6385
        have hw : |(5312682897/10000000000 : ℝ)|=(5312682897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2060084613/10000000000 : ℝ)|^8433 ≤ (12411163071699/100000000000000 : ℝ)^6385
        have hw : |(-2060084613/10000000000 : ℝ)|=(2060084613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078176411/2000000000 : ℝ)|^8433 ≤ (44216997386209/100000000000000 : ℝ)^6385
        have hw : |(1078176411/2000000000 : ℝ)|=(1078176411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s8_6 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312683003/10000000000 : ℝ)*x 0 + (8423253/15625000 : ℝ)*x 1 + (-2060084653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312683003/10000000000 : ℝ)^8433 ≤ (43371840670017/100000000000000 : ℝ)^6385 := by
    have hnat : (5312683003 : ℕ)^8433*100000000000000^6385 ≤ 43371840670017^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312683003 10000000000 43371840670017 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8423253/15625000 : ℝ)^8433 ≤ (11054248980937/25000000000000 : ℝ)^6385 := by
    have hnat : (8423253 : ℕ)^8433*25000000000000^6385 ≤ 11054248980937^6385*15625000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8423253 15625000 11054248980937 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2060084653/10000000000 : ℝ)^8433 ≤ (6205581694989/50000000000000 : ℝ)^6385 := by
    have hnat : (2060084653 : ℕ)^8433*50000000000000^6385 ≤ 6205581694989^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060084653 10000000000 6205581694989 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312683003/10000000000 : ℝ), (8423253/15625000 : ℝ), (-2060084653/10000000000 : ℝ)] ![(43371840670017/100000000000000 : ℝ), (11054248980937/25000000000000 : ℝ), (6205581694989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312683003/10000000000 : ℝ)|^8433 ≤ (43371840670017/100000000000000 : ℝ)^6385
        have hw : |(5312683003/10000000000 : ℝ)|=(5312683003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8423253/15625000 : ℝ)|^8433 ≤ (11054248980937/25000000000000 : ℝ)^6385
        have hw : |(8423253/15625000 : ℝ)|=(8423253/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2060084653/10000000000 : ℝ)|^8433 ≤ (6205581694989/50000000000000 : ℝ)^6385
        have hw : |(-2060084653/10000000000 : ℝ)|=(2060084653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s8_7 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4351058883/10000000000 : ℝ)*x 0 + (4477873541/10000000000 : ℝ)*x 1 + (1056939891/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351058883/10000000000 : ℝ)^8433 ≤ (33317595981069/100000000000000 : ℝ)^6385 := by
    have hnat : (4351058883 : ℕ)^8433*100000000000000^6385 ≤ 33317595981069^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351058883 10000000000 33317595981069 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477873541/10000000000 : ℝ)^8433 ≤ (34606087178337/100000000000000 : ℝ)^6385 := by
    have hnat : (4477873541 : ℕ)^8433*100000000000000^6385 ≤ 34606087178337^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477873541 10000000000 34606087178337 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056939891/2500000000 : ℝ)^8433 ≤ (32076316823031/100000000000000 : ℝ)^6385 := by
    have hnat : (1056939891 : ℕ)^8433*100000000000000^6385 ≤ 32076316823031^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056939891 2500000000 32076316823031 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351058883/10000000000 : ℝ), (4477873541/10000000000 : ℝ), (1056939891/2500000000 : ℝ)] ![(33317595981069/100000000000000 : ℝ), (34606087178337/100000000000000 : ℝ), (32076316823031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351058883/10000000000 : ℝ)|^8433 ≤ (33317595981069/100000000000000 : ℝ)^6385
        have hw : |(4351058883/10000000000 : ℝ)|=(4351058883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477873541/10000000000 : ℝ)|^8433 ≤ (34606087178337/100000000000000 : ℝ)^6385
        have hw : |(4477873541/10000000000 : ℝ)|=(4477873541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056939891/2500000000 : ℝ)|^8433 ≤ (32076316823031/100000000000000 : ℝ)^6385
        have hw : |(1056939891/2500000000 : ℝ)|=(1056939891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1240_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2869/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11477/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14103/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2869/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2869/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2869/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2869/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2869/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2869/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2869/25000 : ℝ) ^ (527/128 : ℝ) ≤ (13458025973878461/100000000000000000000 : ℝ) := by
    have hpowers : (2869/25000 : ℝ)^527 ≤ (13458025973878461/100000000000000000000 : ℝ)^128 := by
      have hnat : (2869 : ℕ)^527*100000000000000000000^128 ≤ 13458025973878461^128*25000^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2869 25000 13458025973878461 100000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2869/25000 : ℝ)) (X := (13458025973878461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hpowhi : (1763/12500 : ℝ) ^ (527/128 : ℝ) ≤ (31454497234919719/100000000000000000000 : ℝ) := by
    have hpowers : (1763/12500 : ℝ)^527 ≤ (31454497234919719/100000000000000000000 : ℝ)^128 := by
      have hnat : (1763 : ℕ)^527*100000000000000000000^128 ≤ 31454497234919719^128*12500^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1763 12500 31454497234919719 100000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1763/12500 : ℝ)) (X := (31454497234919719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013458025973878461/50000000000000000000 : ℝ) ≤ (10000653681908517/10000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (50013458025973878461/50000000000000000000 : ℝ)^128 ≤ (10000653681908517/10000000000000000 : ℝ)^527 := by
      have hnat : (50013458025973878461 : ℕ)^128*10000000000000000^527 ≤ 10000653681908517^527*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013458025973878461 50000000000000000000 10000653681908517 10000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000653681908517/10000000000000000 : ℝ)) (X := (50013458025973878461/50000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002245626160439909/5000000000000000000 : ℝ) ≤ (1250136333629433/1250000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (5002245626160439909/5000000000000000000 : ℝ)^128 ≤ (1250136333629433/1250000000000000 : ℝ)^527 := by
      have hnat : (5002245626160439909 : ℕ)^128*1250000000000000^527 ≤ 1250136333629433^527*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002245626160439909 5000000000000000000 1250136333629433 1250000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250136333629433/1250000000000000 : ℝ)) (X := (5002245626160439909/5000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031454497234919719/50000000000000000000 : ℝ) ≤ (10001527656162411/10000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (50031454497234919719/50000000000000000000 : ℝ)^128 ≤ (10001527656162411/10000000000000000 : ℝ)^527 := by
      have hnat : (50031454497234919719 : ℕ)^128*10000000000000000^527 ≤ 10001527656162411^527*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031454497234919719 50000000000000000000 10001527656162411 10000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001527656162411/10000000000000000 : ℝ)) (X := (50031454497234919719/50000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13458025973878461/100000000000000000000 : ℝ) ≤ ((2189307345626491261/2190000000000000000 : ℝ)+2*(145662375649/87600000000000 : ℝ)*(2869/25000 : ℝ))^(527/128 : ℝ) := by
    rw [show (2189307345626491261/2190000000000000000 : ℝ)+2*(145662375649/87600000000000 : ℝ)*(2869/25000 : ℝ)=(10000653681908517/10000000000000000 : ℝ) by norm_num, show 1+2*(13458025973878461/100000000000000000000 : ℝ)=(50013458025973878461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31454497234919719/100000000000000000000 : ℝ)+(13458025973878461/100000000000000000000 : ℝ) ≤ ((2189307345626491261/2190000000000000000 : ℝ)+(145662375649/87600000000000 : ℝ)*((1763/12500 : ℝ)+(2869/25000 : ℝ)))^(527/128 : ℝ) := by
    rw [show (2189307345626491261/2190000000000000000 : ℝ)+(145662375649/87600000000000 : ℝ)*((1763/12500 : ℝ)+(2869/25000 : ℝ))=(1250136333629433/1250000000000000 : ℝ) by norm_num, show 1+(31454497234919719/100000000000000000000 : ℝ)+(13458025973878461/100000000000000000000 : ℝ)=(5002245626160439909/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31454497234919719/100000000000000000000 : ℝ) ≤ ((2189307345626491261/2190000000000000000 : ℝ)+2*(145662375649/87600000000000 : ℝ)*(1763/12500 : ℝ))^(527/128 : ℝ) := by
    rw [show (2189307345626491261/2190000000000000000 : ℝ)+2*(145662375649/87600000000000 : ℝ)*(1763/12500 : ℝ)=(10001527656162411/10000000000000000 : ℝ) by norm_num, show 1+2*(31454497234919719/100000000000000000000 : ℝ)=(50031454497234919719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2189307345626491261/2190000000000000000 : ℝ)*(X 1 0+X 2 0)+(145662375649/87600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (2869/25000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (2189307345626491261/2190000000000000000 : ℝ)) (alpha := (145662375649/87600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2189307345626491261/2190000000000000000 : ℝ)*(X 0 1+X 2 1)+(145662375649/87600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (2869/25000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (2189307345626491261/2190000000000000000 : ℝ)) (alpha := (145662375649/87600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2189307345626491261/2190000000000000000 : ℝ)*(X 0 2+X 1 2)+(145662375649/87600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (2869/25000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (2189307345626491261/2190000000000000000 : ℝ)) (alpha := (145662375649/87600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1325553/6250000 : ℝ)*X 0 0+(2695597743/5000000000 : ℝ)*X 0 1+(5267226349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672155047/5000000000 : ℝ)*X 1 0+(-1091870149/5000000000 : ℝ)*X 1 1+(2633613153/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068862019/2000000000 : ℝ)*X 2 0+(1316806581/2500000000 : ℝ)*X 2 1+(-2183740273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087762371/2500000000 : ℝ)*X 0 0+(264195237/625000000 : ℝ)*X 0 1+(4478506983/10000000000 : ℝ)*X 0 2+(1087762371/2500000000 : ℝ)*X 1 0+(264195237/625000000 : ℝ)*X 1 1+(4478506983/10000000000 : ℝ)*X 1 2+(1087762371/2500000000 : ℝ)*X 2 0+(264195237/625000000 : ℝ)*X 2 1+(4478506983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2120889479/10000000000 : ℝ)*X 0 0+(526753881/1000000000 : ℝ)*X 0 1+(2695440937/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312682897/10000000000 : ℝ)*X 1 0+(-2060084613/10000000000 : ℝ)*X 1 1+(1078176411/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312683003/10000000000 : ℝ)*X 2 0+(8423253/15625000 : ℝ)*X 2 1+(-2060084653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351058883/10000000000 : ℝ)*X 0 0+(4477873541/10000000000 : ℝ)*X 0 1+(1056939891/2500000000 : ℝ)*X 0 2+(4351058883/10000000000 : ℝ)*X 1 0+(4477873541/10000000000 : ℝ)*X 1 1+(1056939891/2500000000 : ℝ)*X 1 2+(4351058883/10000000000 : ℝ)*X 2 0+(4477873541/10000000000 : ℝ)*X 2 1+(1056939891/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (109339868858031602988965613/36500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (277601577/50000000000000 : ℝ)*(base19) + (478096891/100000000000000 : ℝ)*(base23) + (21007317/50000000000000 : ℝ)*(lower2) + (13038331/20000000000000 : ℝ)*(upper3) + (24549529/50000000000000 : ℝ)*(upper5) + (6022277921264033/100000000000000 : ℝ)*(major0) + (6022277921264033/100000000000000 : ℝ)*(major1) + (6022277921264033/100000000000000 : ℝ)*(major2) + (8066536479592529/100000000000000 : ℝ)*(sp0) + (806654909705363/10000000000000 : ℝ)*(sp1) + (8066549174159893/100000000000000 : ℝ)*(sp2) + (397799799658073/10000000000000 : ℝ)*(sp3) + (2634532851/20000000000000 : ℝ)*(sp4) + (505864799/6250000000000 : ℝ)*(sp7) + (3978006090417513/100000000000000 : ℝ)*(f.failure) + (504159353266049/6250000000000 : ℝ)*(f.sum) + (11985406289443/4380000000000000000000000000 : ℝ)*base66 + (1067614471553459387/219000000000000000000000000000000 : ℝ)*base68 + (2143994940224459387/219000000000000000000000000000000 : ℝ)*base70 + (2349622045769459387/219000000000000000000000000000000 : ℝ)*base72 + (23264766622097/4380000000000000000000000000 : ℝ)*base73 + (1594503626484540613/219000000000000000000000000000000 : ℝ)*base75 + (95364337545540613/219000000000000000000000000000000 : ℝ)*base77 + (3524414000225459387/219000000000000000000000000000000 : ℝ)*base80 + (17793749386843/4380000000000000000000000000 : ℝ)*base82 + (35444167/10000000000000000000000 : ℝ)*base89 + (35444167/10000000000000000000000 : ℝ)*base91 + (35444167/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2777471341316736137019/365000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1194843611/100000000000000 : ℝ)*(base19) + (1475606319/100000000000000 : ℝ)*(base23) + (91599927/20000000000000 : ℝ)*(lower1) + (239462229/100000000000000 : ℝ)*(upper3) + (39147241/100000000000000 : ℝ)*(lower4) + (8485563/12500000000000 : ℝ)*(upper5) + (94574895897383/1562500000000 : ℝ)*(major0) + (94574895897383/1562500000000 : ℝ)*(major1) + (94574895897383/1562500000000 : ℝ)*(major2) + (7611960931/100000000000000 : ℝ)*(sp2) + (2026855855310703/25000000000000 : ℝ)*(sp4) + (8107422226399201/100000000000000 : ℝ)*(sp5) + (8107414333675563/100000000000000 : ℝ)*(sp6) + (1999081499985911/50000000000000 : ℝ)*(sp7) + (1999081499985911/50000000000000 : ℝ)*(f.failure) + (2026855855310703/25000000000000 : ℝ)*(f.sum) + (2113294329331/547500000000000000000000000 : ℝ)*base65 + (308462510594288713/3421875000000000000000000000000 : ℝ)*base67 + (16421593662055037/3421875000000000000000000000000 : ℝ)*base70 + (180417727410277169/1710937500000000000000000000000 : ℝ)*base71 + (4975407024617/1095000000000000000000000000 : ℝ)*base73 + (227507898333941581/1710937500000000000000000000000 : ℝ)*base76 + (41546153956444963/3421875000000000000000000000000 : ℝ)*base77 + (6698113461898787/3421875000000000000000000000000 : ℝ)*base80 + (767168711251/547500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (24678951/5000000000000000000000 : ℝ)*base90 + (24678951/5000000000000000000000 : ℝ)*base92 + (24678951/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1240_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2869/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1240_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1240_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1240_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1240_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1240_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1240_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
