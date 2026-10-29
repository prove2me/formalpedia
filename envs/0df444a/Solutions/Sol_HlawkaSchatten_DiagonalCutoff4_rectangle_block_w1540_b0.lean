-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1540_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:07:27.147581+00:00
-- url     : https://prove2.me/submissions/6bbf1fc8-cb56-47a7-9886-84c1c1ddeed7

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
theorem support_rectangle_w1540_s0_0 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-828267821/5000000000 : ℝ)*x 0 + (2945796657/5000000000 : ℝ)*x 1 + (4867112851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (828267821/5000000000 : ℝ)^4577 ≤ (4933315300597/50000000000000 : ℝ)^3553 := by
    have hnat : (828267821 : ℕ)^4577*50000000000000^3553 ≤ 4933315300597^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828267821 5000000000 4933315300597 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2945796657/5000000000 : ℝ)^4577 ≤ (50583887122559/100000000000000 : ℝ)^3553 := by
    have hnat : (2945796657 : ℕ)^4577*100000000000000^3553 ≤ 50583887122559^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2945796657 5000000000 50583887122559 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4867112851/10000000000 : ℝ)^4577 ≤ (19774741130607/50000000000000 : ℝ)^3553 := by
    have hnat : (4867112851 : ℕ)^4577*50000000000000^3553 ≤ 19774741130607^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4867112851 10000000000 19774741130607 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-828267821/5000000000 : ℝ), (2945796657/5000000000 : ℝ), (4867112851/10000000000 : ℝ)] ![(4933315300597/50000000000000 : ℝ), (50583887122559/100000000000000 : ℝ), (19774741130607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-828267821/5000000000 : ℝ)|^4577 ≤ (4933315300597/50000000000000 : ℝ)^3553
        have hw : |(-828267821/5000000000 : ℝ)|=(828267821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2945796657/5000000000 : ℝ)|^4577 ≤ (50583887122559/100000000000000 : ℝ)^3553
        have hw : |(2945796657/5000000000 : ℝ)|=(2945796657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4867112851/10000000000 : ℝ)|^4577 ≤ (19774741130607/50000000000000 : ℝ)^3553
        have hw : |(4867112851/10000000000 : ℝ)|=(4867112851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s0_1 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1367978423/2500000000 : ℝ)*x 0 + (-1114370541/5000000000 : ℝ)*x 1 + (4867112911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1367978423/2500000000 : ℝ)^4577 ≤ (11497650523473/25000000000000 : ℝ)^3553 := by
    have hnat : (1367978423 : ℕ)^4577*25000000000000^3553 ≤ 11497650523473^3553*2500000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367978423 2500000000 11497650523473 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114370541/5000000000 : ℝ)^4577 ≤ (7229957495873/50000000000000 : ℝ)^3553 := by
    have hnat : (1114370541 : ℕ)^4577*50000000000000^3553 ≤ 7229957495873^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114370541 5000000000 7229957495873 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4867112911/10000000000 : ℝ)^4577 ≤ (19774741444641/50000000000000 : ℝ)^3553 := by
    have hnat : (4867112911 : ℕ)^4577*50000000000000^3553 ≤ 19774741444641^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4867112911 10000000000 19774741444641 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1367978423/2500000000 : ℝ), (-1114370541/5000000000 : ℝ), (4867112911/10000000000 : ℝ)] ![(11497650523473/25000000000000 : ℝ), (7229957495873/50000000000000 : ℝ), (19774741444641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1367978423/2500000000 : ℝ)|^4577 ≤ (11497650523473/25000000000000 : ℝ)^3553
        have hw : |(1367978423/2500000000 : ℝ)|=(1367978423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1114370541/5000000000 : ℝ)|^4577 ≤ (7229957495873/50000000000000 : ℝ)^3553
        have hw : |(-1114370541/5000000000 : ℝ)|=(1114370541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4867112911/10000000000 : ℝ)|^4577 ≤ (19774741444641/50000000000000 : ℝ)^3553
        have hw : |(4867112911/10000000000 : ℝ)|=(4867112911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s0_2 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5471913631/10000000000 : ℝ)*x 0 + (4867112883/10000000000 : ℝ)*x 1 + (-2228741197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5471913631/10000000000 : ℝ)^4577 ≤ (22995300716717/50000000000000 : ℝ)^3553 := by
    have hnat : (5471913631 : ℕ)^4577*50000000000000^3553 ≤ 22995300716717^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471913631 10000000000 22995300716717 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4867112883/10000000000 : ℝ)^4577 ≤ (39549482596183/100000000000000 : ℝ)^3553 := by
    have hnat : (4867112883 : ℕ)^4577*100000000000000^3553 ≤ 39549482596183^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4867112883 10000000000 39549482596183 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2228741197/10000000000 : ℝ)^4577 ≤ (14459915952893/100000000000000 : ℝ)^3553 := by
    have hnat : (2228741197 : ℕ)^4577*100000000000000^3553 ≤ 14459915952893^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228741197 10000000000 14459915952893 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5471913631/10000000000 : ℝ), (4867112883/10000000000 : ℝ), (-2228741197/10000000000 : ℝ)] ![(22995300716717/50000000000000 : ℝ), (39549482596183/100000000000000 : ℝ), (14459915952893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5471913631/10000000000 : ℝ)|^4577 ≤ (22995300716717/50000000000000 : ℝ)^3553
        have hw : |(5471913631/10000000000 : ℝ)|=(5471913631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4867112883/10000000000 : ℝ)|^4577 ≤ (39549482596183/100000000000000 : ℝ)^3553
        have hw : |(4867112883/10000000000 : ℝ)|=(4867112883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2228741197/10000000000 : ℝ)|^4577 ≤ (14459915952893/100000000000000 : ℝ)^3553
        have hw : |(-2228741197/10000000000 : ℝ)|=(2228741197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s0_3 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (413767677/1000000000 : ℝ)*x 0 + (772959447/2500000000 : ℝ)*x 1 + (5460842481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413767677/1000000000 : ℝ)^4577 ≤ (3208507525653/10000000000000 : ℝ)^3553 := by
    have hnat : (413767677 : ℕ)^4577*10000000000000^3553 ≤ 3208507525653^3553*1000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413767677 1000000000 3208507525653 10000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772959447/2500000000 : ℝ)^4577 ≤ (2755519714453/12500000000000 : ℝ)^3553 := by
    have hnat : (772959447 : ℕ)^4577*12500000000000^3553 ≤ 2755519714453^3553*2500000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772959447 2500000000 2755519714453 12500000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460842481/10000000000 : ℝ)^4577 ≤ (22935383504713/50000000000000 : ℝ)^3553 := by
    have hnat : (5460842481 : ℕ)^4577*50000000000000^3553 ≤ 22935383504713^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460842481 10000000000 22935383504713 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(413767677/1000000000 : ℝ), (772959447/2500000000 : ℝ), (5460842481/10000000000 : ℝ)] ![(3208507525653/10000000000000 : ℝ), (2755519714453/12500000000000 : ℝ), (22935383504713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(413767677/1000000000 : ℝ)|^4577 ≤ (3208507525653/10000000000000 : ℝ)^3553
        have hw : |(413767677/1000000000 : ℝ)|=(413767677/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(772959447/2500000000 : ℝ)|^4577 ≤ (2755519714453/12500000000000 : ℝ)^3553
        have hw : |(772959447/2500000000 : ℝ)|=(772959447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460842481/10000000000 : ℝ)|^4577 ≤ (22935383504713/50000000000000 : ℝ)^3553
        have hw : |(5460842481/10000000000 : ℝ)|=(5460842481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s0_4 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-829912553/5000000000 : ℝ)*x 0 + (611637401/1250000000 : ℝ)*x 1 + (2932339843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (829912553/5000000000 : ℝ)^4577 ≤ (2472969303589/25000000000000 : ℝ)^3553 := by
    have hnat : (829912553 : ℕ)^4577*25000000000000^3553 ≤ 2472969303589^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829912553 5000000000 2472969303589 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (611637401/1250000000 : ℝ)^4577 ≤ (39821711071339/100000000000000 : ℝ)^3553 := by
    have hnat : (611637401 : ℕ)^4577*100000000000000^3553 ≤ 39821711071339^3553*1250000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611637401 1250000000 39821711071339 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2932339843/5000000000 : ℝ)^4577 ≤ (5028641169683/10000000000000 : ℝ)^3553 := by
    have hnat : (2932339843 : ℕ)^4577*10000000000000^3553 ≤ 5028641169683^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2932339843 5000000000 5028641169683 10000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-829912553/5000000000 : ℝ), (611637401/1250000000 : ℝ), (2932339843/5000000000 : ℝ)] ![(2472969303589/25000000000000 : ℝ), (39821711071339/100000000000000 : ℝ), (5028641169683/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-829912553/5000000000 : ℝ)|^4577 ≤ (2472969303589/25000000000000 : ℝ)^3553
        have hw : |(-829912553/5000000000 : ℝ)|=(829912553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(611637401/1250000000 : ℝ)|^4577 ≤ (39821711071339/100000000000000 : ℝ)^3553
        have hw : |(611637401/1250000000 : ℝ)|=(611637401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2932339843/5000000000 : ℝ)|^4577 ≤ (5028641169683/10000000000000 : ℝ)^3553
        have hw : |(2932339843/5000000000 : ℝ)|=(2932339843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s0_5 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5191911787/10000000000 : ℝ)*x 0 + (-1231174321/10000000000 : ℝ)*x 1 + (1172935959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5191911787/10000000000 : ℝ)^4577 ≤ (21490801040421/50000000000000 : ℝ)^3553 := by
    have hnat : (5191911787 : ℕ)^4577*50000000000000^3553 ≤ 21490801040421^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191911787 10000000000 21490801040421 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1231174321/10000000000 : ℝ)^4577 ≤ (6731984996981/100000000000000 : ℝ)^3553 := by
    have hnat : (1231174321 : ℕ)^4577*100000000000000^3553 ≤ 6731984996981^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231174321 10000000000 6731984996981 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1172935959/2000000000 : ℝ)^4577 ≤ (6285801612601/12500000000000 : ℝ)^3553 := by
    have hnat : (1172935959 : ℕ)^4577*12500000000000^3553 ≤ 6285801612601^3553*2000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1172935959 2000000000 6285801612601 12500000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5191911787/10000000000 : ℝ), (-1231174321/10000000000 : ℝ), (1172935959/2000000000 : ℝ)] ![(21490801040421/50000000000000 : ℝ), (6731984996981/100000000000000 : ℝ), (6285801612601/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5191911787/10000000000 : ℝ)|^4577 ≤ (21490801040421/50000000000000 : ℝ)^3553
        have hw : |(5191911787/10000000000 : ℝ)|=(5191911787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1231174321/10000000000 : ℝ)|^4577 ≤ (6731984996981/100000000000000 : ℝ)^3553
        have hw : |(-1231174321/10000000000 : ℝ)|=(1231174321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1172935959/2000000000 : ℝ)|^4577 ≤ (6285801612601/12500000000000 : ℝ)^3553
        have hw : |(1172935959/2000000000 : ℝ)|=(1172935959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s0_6 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5191910837/10000000000 : ℝ)*x 0 + (5864681109/10000000000 : ℝ)*x 1 + (-1231173699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5191910837/10000000000 : ℝ)^4577 ≤ (10745397987389/25000000000000 : ℝ)^3553 := by
    have hnat : (5191910837 : ℕ)^4577*25000000000000^3553 ≤ 10745397987389^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191910837 10000000000 10745397987389 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5864681109/10000000000 : ℝ)^4577 ≤ (50286427414819/100000000000000 : ℝ)^3553 := by
    have hnat : (5864681109 : ℕ)^4577*100000000000000^3553 ≤ 50286427414819^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5864681109 10000000000 50286427414819 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1231173699/10000000000 : ℝ)^4577 ≤ (3365990307857/50000000000000 : ℝ)^3553 := by
    have hnat : (1231173699 : ℕ)^4577*50000000000000^3553 ≤ 3365990307857^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231173699 10000000000 3365990307857 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5191910837/10000000000 : ℝ), (5864681109/10000000000 : ℝ), (-1231173699/10000000000 : ℝ)] ![(10745397987389/25000000000000 : ℝ), (50286427414819/100000000000000 : ℝ), (3365990307857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5191910837/10000000000 : ℝ)|^4577 ≤ (10745397987389/25000000000000 : ℝ)^3553
        have hw : |(5191910837/10000000000 : ℝ)|=(5191910837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5864681109/10000000000 : ℝ)|^4577 ≤ (50286427414819/100000000000000 : ℝ)^3553
        have hw : |(5864681109/10000000000 : ℝ)|=(5864681109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1231173699/10000000000 : ℝ)|^4577 ≤ (3365990307857/50000000000000 : ℝ)^3553
        have hw : |(-1231173699/10000000000 : ℝ)|=(1231173699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s0_7 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4145280519/10000000000 : ℝ)*x 0 + (5400750767/10000000000 : ℝ)*x 1 + (3154070423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4145280519/10000000000 : ℝ)^4577 ≤ (6432210198709/20000000000000 : ℝ)^3553 := by
    have hnat : (4145280519 : ℕ)^4577*20000000000000^3553 ≤ 6432210198709^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145280519 10000000000 6432210198709 20000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400750767/10000000000 : ℝ)^4577 ≤ (11305389096197/25000000000000 : ℝ)^3553 := by
    have hnat : (5400750767 : ℕ)^4577*25000000000000^3553 ≤ 11305389096197^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400750767 10000000000 11305389096197 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154070423/10000000000 : ℝ)^4577 ≤ (4523478520581/20000000000000 : ℝ)^3553 := by
    have hnat : (3154070423 : ℕ)^4577*20000000000000^3553 ≤ 4523478520581^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154070423 10000000000 4523478520581 20000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4145280519/10000000000 : ℝ), (5400750767/10000000000 : ℝ), (3154070423/10000000000 : ℝ)] ![(6432210198709/20000000000000 : ℝ), (11305389096197/25000000000000 : ℝ), (4523478520581/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4145280519/10000000000 : ℝ)|^4577 ≤ (6432210198709/20000000000000 : ℝ)^3553
        have hw : |(4145280519/10000000000 : ℝ)|=(4145280519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400750767/10000000000 : ℝ)|^4577 ≤ (11305389096197/25000000000000 : ℝ)^3553
        have hw : |(5400750767/10000000000 : ℝ)|=(5400750767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154070423/10000000000 : ℝ)|^4577 ≤ (4523478520581/20000000000000 : ℝ)^3553
        have hw : |(3154070423/10000000000 : ℝ)|=(3154070423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1540_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3181/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25127/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4575/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4575 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4575*1^1024 ≤ 0^1024*1^4575 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4575 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4575/1024 : ℝ) ≤ (166760888177598667/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4575 ≤ (166760888177598667/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4575*10000000000000000000^1024 ≤ 166760888177598667^1024*5^4575 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 166760888177598667 10000000000000000000 4575 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (166760888177598667/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4575 := by
      have hnat : (1 : ℕ)^1024*1^4575 ≤ 1^4575*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10166760888177598667/10000000000000000000 : ℝ) ≤ (2509271518823049/2500000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (10166760888177598667/10000000000000000000 : ℝ)^1024 ≤ (2509271518823049/2500000000000000 : ℝ)^4575 := by
      have hnat : (10166760888177598667 : ℕ)^1024*2500000000000000^4575 ≤ 2509271518823049^4575*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10166760888177598667 10000000000000000000 2509271518823049 2500000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2509271518823049/2500000000000000 : ℝ)) (X := (10166760888177598667/10000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5166760888177598667/5000000000000000000 : ℝ) ≤ (1259271518823049/1250000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (5166760888177598667/5000000000000000000 : ℝ)^1024 ≤ (1259271518823049/1250000000000000 : ℝ)^4575 := by
      have hnat : (5166760888177598667 : ℕ)^1024*1250000000000000^4575 ≤ 1259271518823049^4575*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5166760888177598667 5000000000000000000 1259271518823049 1250000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1259271518823049/1250000000000000 : ℝ)) (X := (5166760888177598667/5000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9271518823049/1000000000000000 : ℝ)*(0 : ℝ))^(4575/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9271518823049/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(166760888177598667/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9271518823049/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4575/1024 : ℝ) := by
    rw [show (1 : ℝ)+(9271518823049/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2509271518823049/2500000000000000 : ℝ) by norm_num, show 1+(166760888177598667/10000000000000000000 : ℝ)+(0 : ℝ)=(10166760888177598667/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(166760888177598667/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9271518823049/1000000000000000 : ℝ)*(2/5 : ℝ))^(4575/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9271518823049/1000000000000000 : ℝ)*(2/5 : ℝ)=(1259271518823049/1250000000000000 : ℝ) by norm_num, show 1+2*(166760888177598667/10000000000000000000 : ℝ)=(5166760888177598667/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9271518823049/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9271518823049/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9271518823049/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9271518823049/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9271518823049/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9271518823049/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-828267821/5000000000 : ℝ)*X 0 0+(2945796657/5000000000 : ℝ)*X 0 1+(4867112851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1367978423/2500000000 : ℝ)*X 1 0+(-1114370541/5000000000 : ℝ)*X 1 1+(4867112911/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5471913631/10000000000 : ℝ)*X 2 0+(4867112883/10000000000 : ℝ)*X 2 1+(-2228741197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((413767677/1000000000 : ℝ)*X 0 0+(772959447/2500000000 : ℝ)*X 0 1+(5460842481/10000000000 : ℝ)*X 0 2+(413767677/1000000000 : ℝ)*X 1 0+(772959447/2500000000 : ℝ)*X 1 1+(5460842481/10000000000 : ℝ)*X 1 2+(413767677/1000000000 : ℝ)*X 2 0+(772959447/2500000000 : ℝ)*X 2 1+(5460842481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-829912553/5000000000 : ℝ)*X 0 0+(611637401/1250000000 : ℝ)*X 0 1+(2932339843/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5191911787/10000000000 : ℝ)*X 1 0+(-1231174321/10000000000 : ℝ)*X 1 1+(1172935959/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5191910837/10000000000 : ℝ)*X 2 0+(5864681109/10000000000 : ℝ)*X 2 1+(-1231173699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4145280519/10000000000 : ℝ)*X 0 0+(5400750767/10000000000 : ℝ)*X 0 1+(3154070423/10000000000 : ℝ)*X 0 2+(4145280519/10000000000 : ℝ)*X 1 0+(5400750767/10000000000 : ℝ)*X 1 1+(3154070423/10000000000 : ℝ)*X 1 2+(4145280519/10000000000 : ℝ)*X 2 0+(5400750767/10000000000 : ℝ)*X 2 1+(3154070423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63207584253045569473629/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12415637/20000000000000 : ℝ)*(base1) + (1028517863/100000000000000 : ℝ)*(base19) + (508818171/50000000000000 : ℝ)*(base23) + (74699307/50000000000000 : ℝ)*(upper3) + (28195923/25000000000000 : ℝ)*(upper5) + (174779139704769/25000000000000 : ℝ)*(major0) + (174779139704769/25000000000000 : ℝ)*(major1) + (174779139704769/25000000000000 : ℝ)*(major2) + (976108152888311/100000000000000 : ℝ)*(sp0) + (976110612635919/100000000000000 : ℝ)*(sp1) + (762586424623/78125000000 : ℝ)*(sp2) + (211059816752989/50000000000000 : ℝ)*(sp3) + (443792957/12500000000000 : ℝ)*(sp4) + (322469329/20000000000000 : ℝ)*(sp7) + (52765163491351/12500000000000 : ℝ)*(f.failure) + (488055820576891/50000000000000 : ℝ)*(f.sum) + (31462432791819/12500000000000000000000000000 : ℝ)*base66 + (211768299604319/25000000000000000000000000000 : ℝ)*base68 + (47984489170681/25000000000000000000000000000 : ℝ)*base69 + (163559356654319/25000000000000000000000000000 : ℝ)*base72 + (78048275341819/12500000000000000000000000000 : ℝ)*base74 + (7247849129319/25000000000000000000000000000 : ℝ)*base76 + (56437398954319/25000000000000000000000000000 : ℝ)*base78 + (232303360054319/25000000000000000000000000000 : ℝ)*base80 + (18228505258181/12500000000000000000000000000 : ℝ)*base81 + (579761/625000000000000000000 : ℝ)*base89 + (579761/625000000000000000000 : ℝ)*base91 + (579761/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37525050369739896911997/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1865322877/100000000000000 : ℝ)*(base19) + (2081479201/100000000000000 : ℝ)*(base23) + (425068689/100000000000000 : ℝ)*(base39) + (125828353/50000000000000 : ℝ)*(upper3) + (58806843/12500000000000 : ℝ)*(upper5) + (73717454634483/10000000000000 : ℝ)*(major0) + (73717454634483/10000000000000 : ℝ)*(major1) + (737174121276141/100000000000000 : ℝ)*(major2) + (332642379/6250000000000 : ℝ)*(sp1) + (1270333541/25000000000000 : ℝ)*(sp2) + (32163999486091/3125000000000 : ℝ)*(sp4) + (102924079595397/10000000000000 : ℝ)*(sp5) + (205848249162047/20000000000000 : ℝ)*(sp6) + (445100433899047/100000000000000 : ℝ)*(sp7) + (445100433899047/100000000000000 : ℝ)*(f.failure) + (1029248408623601/100000000000000 : ℝ)*(f.sum) + (178886278460579/100000000000000000000000000000 : ℝ)*base65 + (34158629926091/100000000000000000000000000000 : ℝ)*base68 + (78049605468667/10000000000000000000000000000 : ℝ)*base69 + (694888037473909/100000000000000000000000000000 : ℝ)*base71 + (79618192539421/100000000000000000000000000000 : ℝ)*base74 + (54413577248667/10000000000000000000000000000 : ℝ)*base75 + (46460934878667/10000000000000000000000000000 : ℝ)*base77 + (70658605838667/10000000000000000000000000000 : ℝ)*base79 + (27858534058667/5000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (34945183/5000000000000000000000 : ℝ)*base90 + (34945183/5000000000000000000000 : ℝ)*base92 + (34945183/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1540_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3181/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25127/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1540_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1540_s1_0 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-901419587/5000000000 : ℝ)*x 0 + (5552588593/10000000000 : ℝ)*x 1 + (638995303/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (901419587/5000000000 : ℝ)^4577 ≤ (11003186412139/100000000000000 : ℝ)^3553 := by
    have hnat : (901419587 : ℕ)^4577*100000000000000^3553 ≤ 11003186412139^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901419587 5000000000 11003186412139 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5552588593/10000000000 : ℝ)^4577 ≤ (11716483378801/25000000000000 : ℝ)^3553 := by
    have hnat : (5552588593 : ℕ)^4577*25000000000000^3553 ≤ 11716483378801^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5552588593 10000000000 11716483378801 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638995303/1250000000 : ℝ)^4577 ≤ (42130880063259/100000000000000 : ℝ)^3553 := by
    have hnat : (638995303 : ℕ)^4577*100000000000000^3553 ≤ 42130880063259^3553*1250000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638995303 1250000000 42130880063259 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-901419587/5000000000 : ℝ), (5552588593/10000000000 : ℝ), (638995303/1250000000 : ℝ)] ![(11003186412139/100000000000000 : ℝ), (11716483378801/25000000000000 : ℝ), (42130880063259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-901419587/5000000000 : ℝ)|^4577 ≤ (11003186412139/100000000000000 : ℝ)^3553
        have hw : |(-901419587/5000000000 : ℝ)|=(901419587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5552588593/10000000000 : ℝ)|^4577 ≤ (11716483378801/25000000000000 : ℝ)^3553
        have hw : |(5552588593/10000000000 : ℝ)|=(5552588593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(638995303/1250000000 : ℝ)|^4577 ≤ (42130880063259/100000000000000 : ℝ)^3553
        have hw : |(638995303/1250000000 : ℝ)|=(638995303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s1_1 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538161391/1000000000 : ℝ)*x 0 + (-2034081257/10000000000 : ℝ)*x 1 + (511195967/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538161391/1000000000 : ℝ)^4577 ≤ (11253810954013/25000000000000 : ℝ)^3553 := by
    have hnat : (538161391 : ℕ)^4577*25000000000000^3553 ≤ 11253810954013^3553*1000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538161391 1000000000 11253810954013 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2034081257/10000000000 : ℝ)^4577 ≤ (3213476333587/25000000000000 : ℝ)^3553 := by
    have hnat : (2034081257 : ℕ)^4577*25000000000000^3553 ≤ 3213476333587^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034081257 10000000000 3213476333587 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511195967/1000000000 : ℝ)^4577 ≤ (42130850824261/100000000000000 : ℝ)^3553 := by
    have hnat : (511195967 : ℕ)^4577*100000000000000^3553 ≤ 42130850824261^3553*1000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511195967 1000000000 42130850824261 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538161391/1000000000 : ℝ), (-2034081257/10000000000 : ℝ), (511195967/1000000000 : ℝ)] ![(11253810954013/25000000000000 : ℝ), (3213476333587/25000000000000 : ℝ), (42130850824261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538161391/1000000000 : ℝ)|^4577 ≤ (11253810954013/25000000000000 : ℝ)^3553
        have hw : |(538161391/1000000000 : ℝ)|=(538161391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2034081257/10000000000 : ℝ)|^4577 ≤ (3213476333587/25000000000000 : ℝ)^3553
        have hw : |(-2034081257/10000000000 : ℝ)|=(2034081257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(511195967/1000000000 : ℝ)|^4577 ≤ (42130850824261/100000000000000 : ℝ)^3553
        have hw : |(511195967/1000000000 : ℝ)|=(511195967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s1_2 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690805549/5000000000 : ℝ)*x 0 + (15974881/31250000 : ℝ)*x 1 + (-406816409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690805549/5000000000 : ℝ)^4577 ≤ (45015213515673/100000000000000 : ℝ)^3553 := by
    have hnat : (2690805549 : ℕ)^4577*100000000000000^3553 ≤ 45015213515673^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690805549 5000000000 45015213515673 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15974881/31250000 : ℝ)^4577 ≤ (42130874712331/100000000000000 : ℝ)^3553 := by
    have hnat : (15974881 : ℕ)^4577*100000000000000^3553 ≤ 42130874712331^3553*31250000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15974881 31250000 42130874712331 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (406816409/2000000000 : ℝ)^4577 ≤ (12853911749083/100000000000000 : ℝ)^3553 := by
    have hnat : (406816409 : ℕ)^4577*100000000000000^3553 ≤ 12853911749083^3553*2000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406816409 2000000000 12853911749083 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690805549/5000000000 : ℝ), (15974881/31250000 : ℝ), (-406816409/2000000000 : ℝ)] ![(45015213515673/100000000000000 : ℝ), (42130874712331/100000000000000 : ℝ), (12853911749083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690805549/5000000000 : ℝ)|^4577 ≤ (45015213515673/100000000000000 : ℝ)^3553
        have hw : |(2690805549/5000000000 : ℝ)|=(2690805549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15974881/31250000 : ℝ)|^4577 ≤ (42130874712331/100000000000000 : ℝ)^3553
        have hw : |(15974881/31250000 : ℝ)|=(15974881/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-406816409/2000000000 : ℝ)|^4577 ≤ (12853911749083/100000000000000 : ℝ)^3553
        have hw : |(-406816409/2000000000 : ℝ)|=(406816409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s1_3 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4239394431/10000000000 : ℝ)*x 0 + (751042097/2000000000 : ℝ)*x 1 + (954822783/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4239394431/10000000000 : ℝ)^4577 ≤ (16552367775229/50000000000000 : ℝ)^3553 := by
    have hnat : (4239394431 : ℕ)^4577*50000000000000^3553 ≤ 16552367775229^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239394431 10000000000 16552367775229 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (751042097/2000000000 : ℝ)^4577 ≤ (14158291486321/50000000000000 : ℝ)^3553 := by
    have hnat : (751042097 : ℕ)^4577*50000000000000^3553 ≤ 14158291486321^3553*2000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751042097 2000000000 14158291486321 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (954822783/2000000000 : ℝ)^4577 ≤ (964467036777/2500000000000 : ℝ)^3553 := by
    have hnat : (954822783 : ℕ)^4577*2500000000000^3553 ≤ 964467036777^3553*2000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954822783 2000000000 964467036777 2500000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4239394431/10000000000 : ℝ), (751042097/2000000000 : ℝ), (954822783/2000000000 : ℝ)] ![(16552367775229/50000000000000 : ℝ), (14158291486321/50000000000000 : ℝ), (964467036777/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4239394431/10000000000 : ℝ)|^4577 ≤ (16552367775229/50000000000000 : ℝ)^3553
        have hw : |(4239394431/10000000000 : ℝ)|=(4239394431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(751042097/2000000000 : ℝ)|^4577 ≤ (14158291486321/50000000000000 : ℝ)^3553
        have hw : |(751042097/2000000000 : ℝ)|=(751042097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(954822783/2000000000 : ℝ)|^4577 ≤ (964467036777/2500000000000 : ℝ)^3553
        have hw : |(954822783/2000000000 : ℝ)|=(954822783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s1_4 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1803093701/10000000000 : ℝ)*x 0 + (2558349741/5000000000 : ℝ)*x 1 + (554777781/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1803093701/10000000000 : ℝ)^4577 ≤ (2751296902331/25000000000000 : ℝ)^3553 := by
    have hnat : (1803093701 : ℕ)^4577*25000000000000^3553 ≤ 2751296902331^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803093701 10000000000 2751296902331 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2558349741/5000000000 : ℝ)^4577 ≤ (10545294936981/25000000000000 : ℝ)^3553 := by
    have hnat : (2558349741 : ℕ)^4577*25000000000000^3553 ≤ 10545294936981^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2558349741 5000000000 10545294936981 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554777781/1000000000 : ℝ)^4577 ≤ (46813632633417/100000000000000 : ℝ)^3553 := by
    have hnat : (554777781 : ℕ)^4577*100000000000000^3553 ≤ 46813632633417^3553*1000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554777781 1000000000 46813632633417 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1803093701/10000000000 : ℝ), (2558349741/5000000000 : ℝ), (554777781/1000000000 : ℝ)] ![(2751296902331/25000000000000 : ℝ), (10545294936981/25000000000000 : ℝ), (46813632633417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1803093701/10000000000 : ℝ)|^4577 ≤ (2751296902331/25000000000000 : ℝ)^3553
        have hw : |(-1803093701/10000000000 : ℝ)|=(1803093701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2558349741/5000000000 : ℝ)|^4577 ≤ (10545294936981/25000000000000 : ℝ)^3553
        have hw : |(2558349741/5000000000 : ℝ)|=(2558349741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(554777781/1000000000 : ℝ)|^4577 ≤ (46813632633417/100000000000000 : ℝ)^3553
        have hw : |(554777781/1000000000 : ℝ)|=(554777781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s1_5 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053035787/2000000000 : ℝ)*x 0 + (-159826597/1000000000 : ℝ)*x 1 + (69347221/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053035787/2000000000 : ℝ)^4577 ≤ (43764544131303/100000000000000 : ℝ)^3553 := by
    have hnat : (1053035787 : ℕ)^4577*100000000000000^3553 ≤ 43764544131303^3553*2000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053035787 2000000000 43764544131303 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (159826597/1000000000 : ℝ)^4577 ≤ (2355456158561/25000000000000 : ℝ)^3553 := by
    have hnat : (159826597 : ℕ)^4577*25000000000000^3553 ≤ 2355456158561^3553*1000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159826597 1000000000 2355456158561 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69347221/125000000 : ℝ)^4577 ≤ (23406815610143/50000000000000 : ℝ)^3553 := by
    have hnat : (69347221 : ℕ)^4577*50000000000000^3553 ≤ 23406815610143^3553*125000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69347221 125000000 23406815610143 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053035787/2000000000 : ℝ), (-159826597/1000000000 : ℝ), (69347221/125000000 : ℝ)] ![(43764544131303/100000000000000 : ℝ), (2355456158561/25000000000000 : ℝ), (23406815610143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053035787/2000000000 : ℝ)|^4577 ≤ (43764544131303/100000000000000 : ℝ)^3553
        have hw : |(1053035787/2000000000 : ℝ)|=(1053035787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-159826597/1000000000 : ℝ)|^4577 ≤ (2355456158561/25000000000000 : ℝ)^3553
        have hw : |(-159826597/1000000000 : ℝ)|=(159826597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(69347221/125000000 : ℝ)|^4577 ≤ (23406815610143/50000000000000 : ℝ)^3553
        have hw : |(69347221/125000000 : ℝ)|=(69347221/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s1_6 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265179471/10000000000 : ℝ)*x 0 + (2773888793/5000000000 : ℝ)*x 1 + (-1598265349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265179471/10000000000 : ℝ)^4577 ≤ (8752909974123/20000000000000 : ℝ)^3553 := by
    have hnat : (5265179471 : ℕ)^4577*20000000000000^3553 ≤ 8752909974123^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265179471 10000000000 8752909974123 20000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2773888793/5000000000 : ℝ)^4577 ≤ (11703407549621/25000000000000 : ℝ)^3553 := by
    have hnat : (2773888793 : ℕ)^4577*25000000000000^3553 ≤ 11703407549621^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2773888793 5000000000 11703407549621 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1598265349/10000000000 : ℝ)^4577 ≤ (9421819918359/100000000000000 : ℝ)^3553 := by
    have hnat : (1598265349 : ℕ)^4577*100000000000000^3553 ≤ 9421819918359^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1598265349 10000000000 9421819918359 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265179471/10000000000 : ℝ), (2773888793/5000000000 : ℝ), (-1598265349/10000000000 : ℝ)] ![(8752909974123/20000000000000 : ℝ), (11703407549621/25000000000000 : ℝ), (9421819918359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265179471/10000000000 : ℝ)|^4577 ≤ (8752909974123/20000000000000 : ℝ)^3553
        have hw : |(5265179471/10000000000 : ℝ)|=(5265179471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2773888793/5000000000 : ℝ)|^4577 ≤ (11703407549621/25000000000000 : ℝ)^3553
        have hw : |(2773888793/5000000000 : ℝ)|=(2773888793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1598265349/10000000000 : ℝ)|^4577 ≤ (9421819918359/100000000000000 : ℝ)^3553
        have hw : |(-1598265349/10000000000 : ℝ)|=(1598265349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s1_7 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2119989941/5000000000 : ℝ)*x 0 + (476315893/1000000000 : ℝ)*x 1 + (3766335343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119989941/5000000000 : ℝ)^4577 ≤ (8277656238107/25000000000000 : ℝ)^3553 := by
    have hnat : (2119989941 : ℕ)^4577*25000000000000^3553 ≤ 8277656238107^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119989941 5000000000 8277656238107 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (476315893/1000000000 : ℝ)^4577 ≤ (7692936108689/20000000000000 : ℝ)^3553 := by
    have hnat : (476315893 : ℕ)^4577*20000000000000^3553 ≤ 7692936108689^3553*1000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476315893 1000000000 7692936108689 20000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3766335343/10000000000 : ℝ)^4577 ≤ (14212347246599/50000000000000 : ℝ)^3553 := by
    have hnat : (3766335343 : ℕ)^4577*50000000000000^3553 ≤ 14212347246599^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3766335343 10000000000 14212347246599 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2119989941/5000000000 : ℝ), (476315893/1000000000 : ℝ), (3766335343/10000000000 : ℝ)] ![(8277656238107/25000000000000 : ℝ), (7692936108689/20000000000000 : ℝ), (14212347246599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2119989941/5000000000 : ℝ)|^4577 ≤ (8277656238107/25000000000000 : ℝ)^3553
        have hw : |(2119989941/5000000000 : ℝ)|=(2119989941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(476315893/1000000000 : ℝ)|^4577 ≤ (7692936108689/20000000000000 : ℝ)^3553
        have hw : |(476315893/1000000000 : ℝ)|=(476315893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3766335343/10000000000 : ℝ)|^4577 ≤ (14212347246599/50000000000000 : ℝ)^3553
        have hw : |(3766335343/10000000000 : ℝ)|=(3766335343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1540_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2179/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9021/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25127/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25127/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25127/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25127/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25127/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25127/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3181/100000 : ℝ) ^ (4575/1024 : ℝ) ≤ (4081536946707/20000000000000000000 : ℝ) := by
    have hpowers : (3181/100000 : ℝ)^4575 ≤ (4081536946707/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3181 : ℕ)^4575*20000000000000000000^1024 ≤ 4081536946707^1024*100000^4575 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3181 100000 4081536946707 20000000000000000000 4575 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3181/100000 : ℝ)) (X := (4081536946707/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25127/100000 : ℝ) ^ (4575/1024 : ℝ) ≤ (208912431637918499/100000000000000000000 : ℝ) := by
    have hpowers : (25127/100000 : ℝ)^4575 ≤ (208912431637918499/100000000000000000000 : ℝ)^1024 := by
      have hnat : (25127 : ℕ)^4575*100000000000000000000^1024 ≤ 208912431637918499^1024*100000^4575 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25127 100000 208912431637918499 100000000000000000000 4575 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25127/100000 : ℝ)) (X := (208912431637918499/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000004081536946707/10000000000000000000 : ℝ) ≤ (500000045677521/500000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (10000004081536946707/10000000000000000000 : ℝ)^1024 ≤ (500000045677521/500000000000000 : ℝ)^4575 := by
      have hnat : (10000004081536946707 : ℕ)^1024*500000000000000^4575 ≤ 500000045677521^4575*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000004081536946707 10000000000000000000 500000045677521 500000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000045677521/500000000000000 : ℝ)) (X := (10000004081536946707/10000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50104466419661326017/50000000000000000000 : ℝ) ≤ (10004672654958053/10000000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (50104466419661326017/50000000000000000000 : ℝ)^1024 ≤ (10004672654958053/10000000000000000 : ℝ)^4575 := by
      have hnat : (50104466419661326017 : ℕ)^1024*10000000000000000^4575 ≤ 10004672654958053^4575*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50104466419661326017 50000000000000000000 10004672654958053 10000000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004672654958053/10000000000000000 : ℝ)) (X := (50104466419661326017/50000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50208912431637918499/50000000000000000000 : ℝ) ≤ (5004672198182843/5000000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (50208912431637918499/50000000000000000000 : ℝ)^1024 ≤ (5004672198182843/5000000000000000 : ℝ)^4575 := by
      have hnat : (50208912431637918499 : ℕ)^1024*5000000000000000^4575 ≤ 5004672198182843^4575*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50208912431637918499 50000000000000000000 5004672198182843 5000000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004672198182843/5000000000000000 : ℝ)) (X := (50208912431637918499/50000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4081536946707/20000000000000000000 : ℝ) ≤ ((109715149214971078087/109730000000000000000 : ℝ)+2*(4671741407633/2194600000000000 : ℝ)*(3181/100000 : ℝ))^(4575/1024 : ℝ) := by
    rw [show (109715149214971078087/109730000000000000000 : ℝ)+2*(4671741407633/2194600000000000 : ℝ)*(3181/100000 : ℝ)=(500000045677521/500000000000000 : ℝ) by norm_num, show 1+2*(4081536946707/20000000000000000000 : ℝ)=(10000004081536946707/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(208912431637918499/100000000000000000000 : ℝ)+(4081536946707/20000000000000000000 : ℝ) ≤ ((109715149214971078087/109730000000000000000 : ℝ)+(4671741407633/2194600000000000 : ℝ)*((25127/100000 : ℝ)+(3181/100000 : ℝ)))^(4575/1024 : ℝ) := by
    rw [show (109715149214971078087/109730000000000000000 : ℝ)+(4671741407633/2194600000000000 : ℝ)*((25127/100000 : ℝ)+(3181/100000 : ℝ))=(10004672654958053/10000000000000000 : ℝ) by norm_num, show 1+(208912431637918499/100000000000000000000 : ℝ)+(4081536946707/20000000000000000000 : ℝ)=(50104466419661326017/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(208912431637918499/100000000000000000000 : ℝ) ≤ ((109715149214971078087/109730000000000000000 : ℝ)+2*(4671741407633/2194600000000000 : ℝ)*(25127/100000 : ℝ))^(4575/1024 : ℝ) := by
    rw [show (109715149214971078087/109730000000000000000 : ℝ)+2*(4671741407633/2194600000000000 : ℝ)*(25127/100000 : ℝ)=(5004672198182843/5000000000000000 : ℝ) by norm_num, show 1+2*(208912431637918499/100000000000000000000 : ℝ)=(50208912431637918499/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (109715149214971078087/109730000000000000000 : ℝ)*(X 1 0+X 2 0)+(4671741407633/2194600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (3181/100000 : ℝ)) (hi := (25127/100000 : ℝ)) (c := (109715149214971078087/109730000000000000000 : ℝ)) (alpha := (4671741407633/2194600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (109715149214971078087/109730000000000000000 : ℝ)*(X 0 1+X 2 1)+(4671741407633/2194600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (3181/100000 : ℝ)) (hi := (25127/100000 : ℝ)) (c := (109715149214971078087/109730000000000000000 : ℝ)) (alpha := (4671741407633/2194600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (109715149214971078087/109730000000000000000 : ℝ)*(X 0 2+X 1 2)+(4671741407633/2194600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (3181/100000 : ℝ)) (hi := (25127/100000 : ℝ)) (c := (109715149214971078087/109730000000000000000 : ℝ)) (alpha := (4671741407633/2194600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-901419587/5000000000 : ℝ)*X 0 0+(5552588593/10000000000 : ℝ)*X 0 1+(638995303/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((538161391/1000000000 : ℝ)*X 1 0+(-2034081257/10000000000 : ℝ)*X 1 1+(511195967/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2690805549/5000000000 : ℝ)*X 2 0+(15974881/31250000 : ℝ)*X 2 1+(-406816409/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4239394431/10000000000 : ℝ)*X 0 0+(751042097/2000000000 : ℝ)*X 0 1+(954822783/2000000000 : ℝ)*X 0 2+(4239394431/10000000000 : ℝ)*X 1 0+(751042097/2000000000 : ℝ)*X 1 1+(954822783/2000000000 : ℝ)*X 1 2+(4239394431/10000000000 : ℝ)*X 2 0+(751042097/2000000000 : ℝ)*X 2 1+(954822783/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1803093701/10000000000 : ℝ)*X 0 0+(2558349741/5000000000 : ℝ)*X 0 1+(554777781/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1053035787/2000000000 : ℝ)*X 1 0+(-159826597/1000000000 : ℝ)*X 1 1+(69347221/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5265179471/10000000000 : ℝ)*X 2 0+(2773888793/5000000000 : ℝ)*X 2 1+(-1598265349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2119989941/5000000000 : ℝ)*X 0 0+(476315893/1000000000 : ℝ)*X 0 1+(3766335343/10000000000 : ℝ)*X 0 2+(2119989941/5000000000 : ℝ)*X 1 0+(476315893/1000000000 : ℝ)*X 1 1+(3766335343/10000000000 : ℝ)*X 1 2+(2119989941/5000000000 : ℝ)*X 2 0+(476315893/1000000000 : ℝ)*X 2 1+(3766335343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3953126827468292467118473197/548650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115217057/20000000000000 : ℝ)*(base1) + (2032037871/100000000000000 : ℝ)*(base19) + (702904897/100000000000000 : ℝ)*(base23) + (73755187/100000000000000 : ℝ)*(upper3) + (14759579/25000000000000 : ℝ)*(upper5) + (1625475335758229/100000000000000 : ℝ)*(major0) + (1625475335758229/100000000000000 : ℝ)*(major1) + (162547533575823/10000000000000 : ℝ)*(major2) + (14184382833311/625000000000 : ℝ)*(sp0) + (453899729041321/20000000000000 : ℝ)*(sp1) + (1134746676013783/50000000000000 : ℝ)*(sp2) + (981448942266893/100000000000000 : ℝ)*(sp3) + (6622312013/100000000000000 : ℝ)*(sp6) + (235746839/100000000000000 : ℝ)*(sp7) + (981449754099017/100000000000000 : ℝ)*(f.failure) + (567375169311119/25000000000000 : ℝ)*(f.sum) + (154461141562313/219460000000000000000000000000 : ℝ)*base66 + (37294201235676327923/10973000000000000000000000000000000 : ℝ)*base67 + (13913348522880475601/1097300000000000000000000000000000 : ℝ)*base69 + (106816732995828327923/10973000000000000000000000000000000 : ℝ)*base71 + (393301088092147/219460000000000000000000000000 : ℝ)*base73 + (7794055243577475601/1097300000000000000000000000000000 : ℝ)*base75 + (15216463225446322077/10973000000000000000000000000000000 : ℝ)*base78 + (37103694481939322077/10973000000000000000000000000000000 : ℝ)*base80 + (116366434365507/109730000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (32957487/5000000000000000000000 : ℝ)*base89 + (32957487/5000000000000000000000 : ℝ)*base91 + (17042513/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63583333738638513496372422063/5486500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1806530061/100000000000000 : ℝ)*(base19) + (9082457/400000000000 : ℝ)*(base23) + (140501617/50000000000000 : ℝ)*(upper3) + (34274471/50000000000000 : ℝ)*(lower4) + (301829669/100000000000000 : ℝ)*(upper5) + (1661475832365517/100000000000000 : ℝ)*(major0) + (1661475832365517/100000000000000 : ℝ)*(major1) + (1661475832365517/100000000000000 : ℝ)*(major2) + (2828859521/25000000000000 : ℝ)*(sp1) + (15735560959/100000000000000 : ℝ)*(sp2) + (289970586983529/12500000000000 : ℝ)*(sp4) + (289968946737511/12500000000000 : ℝ)*(sp5) + (72492084052907/3125000000000 : ℝ)*(sp6) + (125398322820133/12500000000000 : ℝ)*(sp7) + (125398322820133/12500000000000 : ℝ)*(f.failure) + (289970586983529/12500000000000 : ℝ)*(f.sum) + (498855256858419/109730000000000000000000000000 : ℝ)*base66 + (54607229030784175979/10973000000000000000000000000000000 : ℝ)*base67 + (57662556330040175979/10973000000000000000000000000000000 : ℝ)*base69 + (2791057066032175979/10973000000000000000000000000000000 : ℝ)*base71 + (331165514894299/109730000000000000000000000000 : ℝ)*base74 + (12268111512559824021/10973000000000000000000000000000000 : ℝ)*base76 + (27631311281314175979/10973000000000000000000000000000000 : ℝ)*base77 + (30979817480175824021/10973000000000000000000000000000000 : ℝ)*base80 + (371181176345069/109730000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1488163/625000000000000000000 : ℝ)*base89 + (1488163/625000000000000000000 : ℝ)*base91 + (1488163/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1540_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2179/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9021/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1540_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1540_s2_0 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1824319233/10000000000 : ℝ)*x 0 + (5449480361/10000000000 : ℝ)*x 1 + (5201116113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1824319233/10000000000 : ℝ)^4577 ≤ (11172357281277/100000000000000 : ℝ)^3553 := by
    have hnat : (1824319233 : ℕ)^4577*100000000000000^3553 ≤ 11172357281277^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824319233 10000000000 11172357281277 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5449480361/10000000000 : ℝ)^4577 ≤ (571848198777/1250000000000 : ℝ)^3553 := by
    have hnat : (5449480361 : ℕ)^4577*1250000000000^3553 ≤ 571848198777^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449480361 10000000000 571848198777 1250000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5201116113/10000000000 : ℝ)^4577 ≤ (43079786794887/100000000000000 : ℝ)^3553 := by
    have hnat : (5201116113 : ℕ)^4577*100000000000000^3553 ≤ 43079786794887^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201116113 10000000000 43079786794887 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1824319233/10000000000 : ℝ), (5449480361/10000000000 : ℝ), (5201116113/10000000000 : ℝ)] ![(11172357281277/100000000000000 : ℝ), (571848198777/1250000000000 : ℝ), (43079786794887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1824319233/10000000000 : ℝ)|^4577 ≤ (11172357281277/100000000000000 : ℝ)^3553
        have hw : |(-1824319233/10000000000 : ℝ)|=(1824319233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5449480361/10000000000 : ℝ)|^4577 ≤ (571848198777/1250000000000 : ℝ)^3553
        have hw : |(5449480361/10000000000 : ℝ)|=(5449480361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5201116113/10000000000 : ℝ)|^4577 ≤ (43079786794887/100000000000000 : ℝ)^3553
        have hw : |(5201116113/10000000000 : ℝ)|=(5201116113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s2_1 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334699669/625000000 : ℝ)*x 0 + (-97598741/500000000 : ℝ)*x 1 + (520111643/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334699669/625000000 : ℝ)^4577 ≤ (44730768337781/100000000000000 : ℝ)^3553 := by
    have hnat : (334699669 : ℕ)^4577*100000000000000^3553 ≤ 44730768337781^3553*625000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334699669 625000000 44730768337781 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97598741/500000000 : ℝ)^4577 ≤ (3047360367727/25000000000000 : ℝ)^3553 := by
    have hnat : (97598741 : ℕ)^4577*25000000000000^3553 ≤ 3047360367727^3553*500000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97598741 500000000 3047360367727 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520111643/1000000000 : ℝ)^4577 ≤ (43079790177263/100000000000000 : ℝ)^3553 := by
    have hnat : (520111643 : ℕ)^4577*100000000000000^3553 ≤ 43079790177263^3553*1000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520111643 1000000000 43079790177263 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334699669/625000000 : ℝ), (-97598741/500000000 : ℝ), (520111643/1000000000 : ℝ)] ![(44730768337781/100000000000000 : ℝ), (3047360367727/25000000000000 : ℝ), (43079790177263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334699669/625000000 : ℝ)|^4577 ≤ (44730768337781/100000000000000 : ℝ)^3553
        have hw : |(334699669/625000000 : ℝ)|=(334699669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97598741/500000000 : ℝ)|^4577 ≤ (3047360367727/25000000000000 : ℝ)^3553
        have hw : |(-97598741/500000000 : ℝ)|=(97598741/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(520111643/1000000000 : ℝ)|^4577 ≤ (43079790177263/100000000000000 : ℝ)^3553
        have hw : |(520111643/1000000000 : ℝ)|=(520111643/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s2_2 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677597291/5000000000 : ℝ)*x 0 + (5201116419/10000000000 : ℝ)*x 1 + (-1951974997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677597291/5000000000 : ℝ)^4577 ≤ (44730767025047/100000000000000 : ℝ)^3553 := by
    have hnat : (2677597291 : ℕ)^4577*100000000000000^3553 ≤ 44730767025047^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677597291 5000000000 44730767025047 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5201116419/10000000000 : ℝ)^4577 ≤ (21539895029947/50000000000000 : ℝ)^3553 := by
    have hnat : (5201116419 : ℕ)^4577*50000000000000^3553 ≤ 21539895029947^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201116419 10000000000 21539895029947 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1951974997/10000000000 : ℝ)^4577 ≤ (3047360723693/25000000000000 : ℝ)^3553 := by
    have hnat : (1951974997 : ℕ)^4577*25000000000000^3553 ≤ 3047360723693^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951974997 10000000000 3047360723693 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677597291/5000000000 : ℝ), (5201116419/10000000000 : ℝ), (-1951974997/10000000000 : ℝ)] ![(44730767025047/100000000000000 : ℝ), (21539895029947/50000000000000 : ℝ), (3047360723693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677597291/5000000000 : ℝ)|^4577 ≤ (44730767025047/100000000000000 : ℝ)^3553
        have hw : |(2677597291/5000000000 : ℝ)|=(2677597291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5201116419/10000000000 : ℝ)|^4577 ≤ (21539895029947/50000000000000 : ℝ)^3553
        have hw : |(5201116419/10000000000 : ℝ)|=(5201116419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1951974997/10000000000 : ℝ)|^4577 ≤ (3047360723693/25000000000000 : ℝ)^3553
        have hw : |(-1951974997/10000000000 : ℝ)|=(1951974997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s2_3 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (850977257/2000000000 : ℝ)*x 0 + (3975762509/10000000000 : ℝ)*x 1 + (4550076791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (850977257/2000000000 : ℝ)^4577 ≤ (207879101701/625000000000 : ℝ)^3553 := by
    have hnat : (850977257 : ℕ)^4577*625000000000^3553 ≤ 207879101701^3553*2000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850977257 2000000000 207879101701 625000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3975762509/10000000000 : ℝ)^4577 ≤ (30476882413327/100000000000000 : ℝ)^3553 := by
    have hnat : (3975762509 : ℕ)^4577*100000000000000^3553 ≤ 30476882413327^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3975762509 10000000000 30476882413327 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4550076791/10000000000 : ℝ)^4577 ≤ (906561532583/2500000000000 : ℝ)^3553 := by
    have hnat : (4550076791 : ℕ)^4577*2500000000000^3553 ≤ 906561532583^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4550076791 10000000000 906561532583 2500000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(850977257/2000000000 : ℝ), (3975762509/10000000000 : ℝ), (4550076791/10000000000 : ℝ)] ![(207879101701/625000000000 : ℝ), (30476882413327/100000000000000 : ℝ), (906561532583/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(850977257/2000000000 : ℝ)|^4577 ≤ (207879101701/625000000000 : ℝ)^3553
        have hw : |(850977257/2000000000 : ℝ)|=(850977257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3975762509/10000000000 : ℝ)|^4577 ≤ (30476882413327/100000000000000 : ℝ)^3553
        have hw : |(3975762509/10000000000 : ℝ)|=(3975762509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4550076791/10000000000 : ℝ)|^4577 ≤ (906561532583/2500000000000 : ℝ)^3553
        have hw : |(4550076791/10000000000 : ℝ)|=(4550076791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s2_4 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-182436519/1000000000 : ℝ)*x 0 + (1040525901/2000000000 : ℝ)*x 1 + (5447953529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182436519/1000000000 : ℝ)^4577 ≤ (5586359921909/50000000000000 : ℝ)^3553 := by
    have hnat : (182436519 : ℕ)^4577*50000000000000^3553 ≤ 5586359921909^3553*1000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182436519 1000000000 5586359921909 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040525901/2000000000 : ℝ)^4577 ≤ (43095935300667/100000000000000 : ℝ)^3553 := by
    have hnat : (1040525901 : ℕ)^4577*100000000000000^3553 ≤ 43095935300667^3553*2000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040525901 2000000000 43095935300667 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5447953529/10000000000 : ℝ)^4577 ≤ (45731344837619/100000000000000 : ℝ)^3553 := by
    have hnat : (5447953529 : ℕ)^4577*100000000000000^3553 ≤ 45731344837619^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447953529 10000000000 45731344837619 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-182436519/1000000000 : ℝ), (1040525901/2000000000 : ℝ), (5447953529/10000000000 : ℝ)] ![(5586359921909/50000000000000 : ℝ), (43095935300667/100000000000000 : ℝ), (45731344837619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-182436519/1000000000 : ℝ)|^4577 ≤ (5586359921909/50000000000000 : ℝ)^3553
        have hw : |(-182436519/1000000000 : ℝ)|=(182436519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040525901/2000000000 : ℝ)|^4577 ≤ (43095935300667/100000000000000 : ℝ)^3553
        have hw : |(1040525901/2000000000 : ℝ)|=(1040525901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5447953529/10000000000 : ℝ)|^4577 ≤ (45731344837619/100000000000000 : ℝ)^3553
        have hw : |(5447953529/10000000000 : ℝ)|=(5447953529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s2_5 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289724919/10000000000 : ℝ)*x 0 + (-10657111/62500000 : ℝ)*x 1 + (5447952943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289724919/10000000000 : ℝ)^4577 ≤ (2201377540177/5000000000000 : ℝ)^3553 := by
    have hnat : (5289724919 : ℕ)^4577*5000000000000^3553 ≤ 2201377540177^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289724919 10000000000 2201377540177 5000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10657111/62500000 : ℝ)^4577 ≤ (10241110676457/100000000000000 : ℝ)^3553 := by
    have hnat : (10657111 : ℕ)^4577*100000000000000^3553 ≤ 10241110676457^3553*62500000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10657111 62500000 10241110676457 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5447952943/10000000000 : ℝ)^4577 ≤ (11432834625227/25000000000000 : ℝ)^3553 := by
    have hnat : (5447952943 : ℕ)^4577*25000000000000^3553 ≤ 11432834625227^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447952943 10000000000 11432834625227 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289724919/10000000000 : ℝ), (-10657111/62500000 : ℝ), (5447952943/10000000000 : ℝ)] ![(2201377540177/5000000000000 : ℝ), (10241110676457/100000000000000 : ℝ), (11432834625227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289724919/10000000000 : ℝ)|^4577 ≤ (2201377540177/5000000000000 : ℝ)^3553
        have hw : |(5289724919/10000000000 : ℝ)|=(5289724919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10657111/62500000 : ℝ)|^4577 ≤ (10241110676457/100000000000000 : ℝ)^3553
        have hw : |(-10657111/62500000 : ℝ)|=(10657111/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5447952943/10000000000 : ℝ)|^4577 ≤ (11432834625227/25000000000000 : ℝ)^3553
        have hw : |(5447952943/10000000000 : ℝ)|=(5447952943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s2_6 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661215559/1250000000 : ℝ)*x 0 + (1089590579/2000000000 : ℝ)*x 1 + (-1705138447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661215559/1250000000 : ℝ)^4577 ≤ (44027546010791/100000000000000 : ℝ)^3553 := by
    have hnat : (661215559 : ℕ)^4577*100000000000000^3553 ≤ 44027546010791^3553*1250000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661215559 1250000000 44027546010791 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089590579/2000000000 : ℝ)^4577 ≤ (2286566899093/5000000000000 : ℝ)^3553 := by
    have hnat : (1089590579 : ℕ)^4577*5000000000000^3553 ≤ 2286566899093^3553*2000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089590579 2000000000 2286566899093 5000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1705138447/10000000000 : ℝ)^4577 ≤ (2048223198357/20000000000000 : ℝ)^3553 := by
    have hnat : (1705138447 : ℕ)^4577*20000000000000^3553 ≤ 2048223198357^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705138447 10000000000 2048223198357 20000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661215559/1250000000 : ℝ), (1089590579/2000000000 : ℝ), (-1705138447/10000000000 : ℝ)] ![(44027546010791/100000000000000 : ℝ), (2286566899093/5000000000000 : ℝ), (2048223198357/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661215559/1250000000 : ℝ)|^4577 ≤ (44027546010791/100000000000000 : ℝ)^3553
        have hw : |(661215559/1250000000 : ℝ)|=(661215559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1089590579/2000000000 : ℝ)|^4577 ≤ (2286566899093/5000000000000 : ℝ)^3553
        have hw : |(1089590579/2000000000 : ℝ)|=(1089590579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1705138447/10000000000 : ℝ)|^4577 ≤ (2048223198357/20000000000000 : ℝ)^3553
        have hw : |(-1705138447/10000000000 : ℝ)|=(1705138447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s2_7 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4254991557/10000000000 : ℝ)*x 0 + (1136644307/2500000000 : ℝ)*x 1 + (1989646317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4254991557/10000000000 : ℝ)^4577 ≤ (831542909069/2500000000000 : ℝ)^3553 := by
    have hnat : (4254991557 : ℕ)^4577*2500000000000^3553 ≤ 831542909069^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254991557 10000000000 831542909069 2500000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136644307/2500000000 : ℝ)^4577 ≤ (8844369353/24414062500 : ℝ)^3553 := by
    have hnat : (1136644307 : ℕ)^4577*24414062500^3553 ≤ 8844369353^3553*2500000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136644307 2500000000 8844369353 24414062500 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1989646317/5000000000 : ℝ)^4577 ≤ (30511746753263/100000000000000 : ℝ)^3553 := by
    have hnat : (1989646317 : ℕ)^4577*100000000000000^3553 ≤ 30511746753263^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989646317 5000000000 30511746753263 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4254991557/10000000000 : ℝ), (1136644307/2500000000 : ℝ), (1989646317/5000000000 : ℝ)] ![(831542909069/2500000000000 : ℝ), (8844369353/24414062500 : ℝ), (30511746753263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4254991557/10000000000 : ℝ)|^4577 ≤ (831542909069/2500000000000 : ℝ)^3553
        have hw : |(4254991557/10000000000 : ℝ)|=(4254991557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1136644307/2500000000 : ℝ)|^4577 ≤ (8844369353/24414062500 : ℝ)^3553
        have hw : |(1136644307/2500000000 : ℝ)|=(1136644307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1989646317/5000000000 : ℝ)|^4577 ≤ (30511746753263/100000000000000 : ℝ)^3553
        have hw : |(1989646317/5000000000 : ℝ)|=(1989646317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1540_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2179/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5319/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15899/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9021/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2179/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9021/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2179/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9021/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2179/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9021/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2179/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9021/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2179/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9021/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2179/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2179/25000 : ℝ) ^ (4575/1024 : ℝ) ≤ (115201317975409/6250000000000000000 : ℝ) := by
    have hpowers : (2179/25000 : ℝ)^4575 ≤ (115201317975409/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2179 : ℕ)^4575*6250000000000000000^1024 ≤ 115201317975409^1024*25000^4575 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2179 25000 115201317975409 6250000000000000000 4575 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2179/25000 : ℝ)) (X := (115201317975409/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9021/50000 : ℝ) ^ (4575/1024 : ℝ) ≤ (47560722287466369/100000000000000000000 : ℝ) := by
    have hpowers : (9021/50000 : ℝ)^4575 ≤ (47560722287466369/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9021 : ℕ)^4575*100000000000000000000^1024 ≤ 47560722287466369^1024*50000^4575 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9021 50000 47560722287466369 100000000000000000000 4575 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9021/50000 : ℝ)) (X := (47560722287466369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125115201317975409/3125000000000000000 : ℝ) ≤ (10000082510661909/10000000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (3125115201317975409/3125000000000000000 : ℝ)^1024 ≤ (10000082510661909/10000000000000000 : ℝ)^4575 := by
      have hnat : (3125115201317975409 : ℕ)^1024*10000000000000000^4575 ≤ 10000082510661909^4575*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125115201317975409 3125000000000000000 10000082510661909 10000000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000082510661909/10000000000000000 : ℝ)) (X := (3125115201317975409/3125000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049403943375072913/100000000000000000000 : ℝ) ≤ (2000221114497381/2000000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (100049403943375072913/100000000000000000000 : ℝ)^1024 ≤ (2000221114497381/2000000000000000 : ℝ)^4575 := by
      have hnat : (100049403943375072913 : ℕ)^1024*2000000000000000^4575 ≤ 2000221114497381^4575*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049403943375072913 100000000000000000000 2000221114497381 2000000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000221114497381/2000000000000000 : ℝ)) (X := (100049403943375072913/100000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50047560722287466369/50000000000000000000 : ℝ) ≤ (10002128634311901/10000000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (50047560722287466369/50000000000000000000 : ℝ)^1024 ≤ (10002128634311901/10000000000000000 : ℝ)^4575 := by
      have hnat : (50047560722287466369 : ℕ)^1024*10000000000000000^4575 ≤ 10002128634311901^4575*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50047560722287466369 50000000000000000000 10002128634311901 10000000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002128634311901/10000000000000000 : ℝ)) (X := (50047560722287466369/50000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(115201317975409/6250000000000000000 : ℝ) ≤ ((46621467740349816531/46630000000000000000 : ℝ)+2*(255765456249/233150000000000 : ℝ)*(2179/25000 : ℝ))^(4575/1024 : ℝ) := by
    rw [show (46621467740349816531/46630000000000000000 : ℝ)+2*(255765456249/233150000000000 : ℝ)*(2179/25000 : ℝ)=(10000082510661909/10000000000000000 : ℝ) by norm_num, show 1+2*(115201317975409/6250000000000000000 : ℝ)=(3125115201317975409/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47560722287466369/100000000000000000000 : ℝ)+(115201317975409/6250000000000000000 : ℝ) ≤ ((46621467740349816531/46630000000000000000 : ℝ)+(255765456249/233150000000000 : ℝ)*((9021/50000 : ℝ)+(2179/25000 : ℝ)))^(4575/1024 : ℝ) := by
    rw [show (46621467740349816531/46630000000000000000 : ℝ)+(255765456249/233150000000000 : ℝ)*((9021/50000 : ℝ)+(2179/25000 : ℝ))=(2000221114497381/2000000000000000 : ℝ) by norm_num, show 1+(47560722287466369/100000000000000000000 : ℝ)+(115201317975409/6250000000000000000 : ℝ)=(100049403943375072913/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47560722287466369/100000000000000000000 : ℝ) ≤ ((46621467740349816531/46630000000000000000 : ℝ)+2*(255765456249/233150000000000 : ℝ)*(9021/50000 : ℝ))^(4575/1024 : ℝ) := by
    rw [show (46621467740349816531/46630000000000000000 : ℝ)+2*(255765456249/233150000000000 : ℝ)*(9021/50000 : ℝ)=(10002128634311901/10000000000000000 : ℝ) by norm_num, show 1+2*(47560722287466369/100000000000000000000 : ℝ)=(50047560722287466369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46621467740349816531/46630000000000000000 : ℝ)*(X 1 0+X 2 0)+(255765456249/233150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (2179/25000 : ℝ)) (hi := (9021/50000 : ℝ)) (c := (46621467740349816531/46630000000000000000 : ℝ)) (alpha := (255765456249/233150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46621467740349816531/46630000000000000000 : ℝ)*(X 0 1+X 2 1)+(255765456249/233150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (2179/25000 : ℝ)) (hi := (9021/50000 : ℝ)) (c := (46621467740349816531/46630000000000000000 : ℝ)) (alpha := (255765456249/233150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46621467740349816531/46630000000000000000 : ℝ)*(X 0 2+X 1 2)+(255765456249/233150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (2179/25000 : ℝ)) (hi := (9021/50000 : ℝ)) (c := (46621467740349816531/46630000000000000000 : ℝ)) (alpha := (255765456249/233150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1824319233/10000000000 : ℝ)*X 0 0+(5449480361/10000000000 : ℝ)*X 0 1+(5201116113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334699669/625000000 : ℝ)*X 1 0+(-97598741/500000000 : ℝ)*X 1 1+(520111643/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677597291/5000000000 : ℝ)*X 2 0+(5201116419/10000000000 : ℝ)*X 2 1+(-1951974997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((850977257/2000000000 : ℝ)*X 0 0+(3975762509/10000000000 : ℝ)*X 0 1+(4550076791/10000000000 : ℝ)*X 0 2+(850977257/2000000000 : ℝ)*X 1 0+(3975762509/10000000000 : ℝ)*X 1 1+(4550076791/10000000000 : ℝ)*X 1 2+(850977257/2000000000 : ℝ)*X 2 0+(3975762509/10000000000 : ℝ)*X 2 1+(4550076791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-182436519/1000000000 : ℝ)*X 0 0+(1040525901/2000000000 : ℝ)*X 0 1+(5447953529/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289724919/10000000000 : ℝ)*X 1 0+(-10657111/62500000 : ℝ)*X 1 1+(5447952943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661215559/1250000000 : ℝ)*X 2 0+(1089590579/2000000000 : ℝ)*X 2 1+(-1705138447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4254991557/10000000000 : ℝ)*X 0 0+(1136644307/2500000000 : ℝ)*X 0 1+(1989646317/5000000000 : ℝ)*X 0 2+(4254991557/10000000000 : ℝ)*X 1 0+(1136644307/2500000000 : ℝ)*X 1 1+(1989646317/5000000000 : ℝ)*X 1 2+(4254991557/10000000000 : ℝ)*X 2 0+(1136644307/2500000000 : ℝ)*X 2 1+(1989646317/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6720525999206642301422097519/1165750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1124455439/100000000000000 : ℝ)*(base19) + (999914211/100000000000000 : ℝ)*(base23) + (1696167/6250000000000 : ℝ)*(lower2) + (96537547/50000000000000 : ℝ)*(upper3) + (4783169/50000000000000 : ℝ)*(lower4) + (2883803344991633/100000000000000 : ℝ)*(major0) + (2883803344991633/100000000000000 : ℝ)*(major1) + (1441901672495817/50000000000000 : ℝ)*(major2) + (201318428382313/5000000000000 : ℝ)*(sp0) + (503298331647813/12500000000000 : ℝ)*(sp1) + (4026386777723733/100000000000000 : ℝ)*(sp2) + (348242385579043/20000000000000 : ℝ)*(sp3) + (19209991683/100000000000000 : ℝ)*(sp4) + (1698071021/25000000000000 : ℝ)*(sp7) + (1741218720179299/100000000000000 : ℝ)*(f.failure) + (503298472204743/12500000000000 : ℝ)*(f.sum) + (5106446675389/2914375000000000000000000000 : ℝ)*base66 + (9713947814552714877/4663000000000000000000000000000000 : ℝ)*base68 + (28418803964124650827/2331500000000000000000000000000000 : ℝ)*base69 + (20652797425676285123/4663000000000000000000000000000000 : ℝ)*base71 + (17550028266111/11657500000000000000000000000 : ℝ)*base74 + (8572483686185150827/2331500000000000000000000000000000 : ℝ)*base75 + (6201573885656485123/4663000000000000000000000000000000 : ℝ)*base77 + (40106147742178514877/4663000000000000000000000000000000 : ℝ)*base80 + (46060586892717/11657500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (4232389/5000000000000000000000 : ℝ)*base89 + (4232389/5000000000000000000000 : ℝ)*base91 + (45767611/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2966940359365352847726627111/582875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (936253137/50000000000000 : ℝ)*(base19) + (161856869/10000000000000 : ℝ)*(base23) + (17928407/12500000000000 : ℝ)*(upper2) + (54299/500000000000 : ℝ)*(upper3) + (298916149/100000000000000 : ℝ)*(upper5) + (729877947396091/25000000000000 : ℝ)*(major0) + (729877947396091/25000000000000 : ℝ)*(major1) + (729877947396091/25000000000000 : ℝ)*(major2) + (24414781669/100000000000000 : ℝ)*(sp1) + (4910473003/50000000000000 : ℝ)*(sp2) + (2038122099829683/50000000000000 : ℝ)*(sp4) + (2038108956185711/50000000000000 : ℝ)*(sp5) + (4076232760144669/100000000000000 : ℝ)*(sp6) + (440694802459147/25000000000000 : ℝ)*(sp7) + (440694802459147/25000000000000 : ℝ)*(f.failure) + (2038122099829683/50000000000000 : ℝ)*(f.sum) + (6079699179427/1457187500000000000000000000 : ℝ)*base65 + (10646707800137880321/1165750000000000000000000000000000 : ℝ)*base67 + (3796896596023880321/1165750000000000000000000000000000 : ℝ)*base69 + (11691661134435880321/1165750000000000000000000000000000 : ℝ)*base71 + (12559114137153/5828750000000000000000000000 : ℝ)*base73 + (10214217448192380321/1165750000000000000000000000000000 : ℝ)*base75 + (10720086071446380321/1165750000000000000000000000000000 : ℝ)*base77 + (18206310429623630321/1165750000000000000000000000000000 : ℝ)*base79 + (6876548433667/23315000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5794083/1250000000000000000000 : ℝ)*base90 + (5794083/1250000000000000000000 : ℝ)*base92 + (5794083/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1540_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2179/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5319/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1540_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1540_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5319/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1540_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1540_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1540_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5319/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1540_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
