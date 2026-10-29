-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1653_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:16:54.331849+00:00
-- url     : https://prove2.me/submissions/5a2bd8c6-4b7e-4c25-804d-d6958b8c7798

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
theorem support_rectangle_w1653_s0_0 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-371851657/2500000000 : ℝ)*x 0 + (289079599/500000000 : ℝ)*x 1 + (4923591513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (371851657/2500000000 : ℝ)^4931 ≤ (1805339014299/20000000000000 : ℝ)^3907 := by
    have hnat : (371851657 : ℕ)^4931*20000000000000^3907 ≤ 1805339014299^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371851657 2500000000 1805339014299 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (289079599/500000000 : ℝ)^4931 ≤ (1565062188481/3125000000000 : ℝ)^3907 := by
    have hnat : (289079599 : ℕ)^4931*3125000000000^3907 ≤ 1565062188481^3907*500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289079599 500000000 1565062188481 3125000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4923591513/10000000000 : ℝ)^4931 ≤ (32713051907/80000000000 : ℝ)^3907 := by
    have hnat : (4923591513 : ℕ)^4931*80000000000^3907 ≤ 32713051907^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4923591513 10000000000 32713051907 80000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-371851657/2500000000 : ℝ), (289079599/500000000 : ℝ), (4923591513/10000000000 : ℝ)] ![(1805339014299/20000000000000 : ℝ), (1565062188481/3125000000000 : ℝ), (32713051907/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-371851657/2500000000 : ℝ)|^4931 ≤ (1805339014299/20000000000000 : ℝ)^3907
        have hw : |(-371851657/2500000000 : ℝ)|=(371851657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(289079599/500000000 : ℝ)|^4931 ≤ (1565062188481/3125000000000 : ℝ)^3907
        have hw : |(289079599/500000000 : ℝ)|=(289079599/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4923591513/10000000000 : ℝ)|^4931 ≤ (32713051907/80000000000 : ℝ)^3907
        have hw : |(4923591513/10000000000 : ℝ)|=(4923591513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s0_1 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5436348911/10000000000 : ℝ)*x 0 + (-489525139/2500000000 : ℝ)*x 1 + (4923591969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5436348911/10000000000 : ℝ)^4931 ≤ (11584386897361/25000000000000 : ℝ)^3907 := by
    have hnat : (5436348911 : ℕ)^4931*25000000000000^3907 ≤ 11584386897361^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436348911 10000000000 11584386897361 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489525139/2500000000 : ℝ)^4931 ≤ (12771132738343/100000000000000 : ℝ)^3907 := by
    have hnat : (489525139 : ℕ)^4931*100000000000000^3907 ≤ 12771132738343^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489525139 2500000000 12771132738343 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4923591969/10000000000 : ℝ)^4931 ≤ (2555707478969/6250000000000 : ℝ)^3907 := by
    have hnat : (4923591969 : ℕ)^4931*6250000000000^3907 ≤ 2555707478969^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4923591969 10000000000 2555707478969 6250000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5436348911/10000000000 : ℝ), (-489525139/2500000000 : ℝ), (4923591969/10000000000 : ℝ)] ![(11584386897361/25000000000000 : ℝ), (12771132738343/100000000000000 : ℝ), (2555707478969/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5436348911/10000000000 : ℝ)|^4931 ≤ (11584386897361/25000000000000 : ℝ)^3907
        have hw : |(5436348911/10000000000 : ℝ)|=(5436348911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-489525139/2500000000 : ℝ)|^4931 ≤ (12771132738343/100000000000000 : ℝ)^3907
        have hw : |(-489525139/2500000000 : ℝ)|=(489525139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4923591969/10000000000 : ℝ)|^4931 ≤ (2555707478969/6250000000000 : ℝ)^3907
        have hw : |(4923591969/10000000000 : ℝ)|=(4923591969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s0_2 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (543634973/1000000000 : ℝ)*x 0 + (196943653/400000000 : ℝ)*x 1 + (-979050153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543634973/1000000000 : ℝ)^4931 ≤ (23168778199979/50000000000000 : ℝ)^3907 := by
    have hnat : (543634973 : ℕ)^4931*50000000000000^3907 ≤ 23168778199979^3907*1000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543634973 1000000000 23168778199979 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196943653/400000000 : ℝ)^4931 ≤ (817826258263/2000000000000 : ℝ)^3907 := by
    have hnat : (196943653 : ℕ)^4931*2000000000000^3907 ≤ 817826258263^3907*400000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196943653 400000000 817826258263 2000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979050153/5000000000 : ℝ)^4931 ≤ (2554226136087/20000000000000 : ℝ)^3907 := by
    have hnat : (979050153 : ℕ)^4931*20000000000000^3907 ≤ 2554226136087^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979050153 5000000000 2554226136087 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543634973/1000000000 : ℝ), (196943653/400000000 : ℝ), (-979050153/5000000000 : ℝ)] ![(23168778199979/50000000000000 : ℝ), (817826258263/2000000000000 : ℝ), (2554226136087/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543634973/1000000000 : ℝ)|^4931 ≤ (23168778199979/50000000000000 : ℝ)^3907
        have hw : |(543634973/1000000000 : ℝ)|=(543634973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(196943653/400000000 : ℝ)|^4931 ≤ (817826258263/2000000000000 : ℝ)^3907
        have hw : |(196943653/400000000 : ℝ)|=(196943653/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-979050153/5000000000 : ℝ)|^4931 ≤ (2554226136087/20000000000000 : ℝ)^3907
        have hw : |(-979050153/5000000000 : ℝ)|=(979050153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s0_3 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4089213761/10000000000 : ℝ)*x 0 + (3083365887/10000000000 : ℝ)*x 1 + (531162143/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4089213761/10000000000 : ℝ)^4931 ≤ (16174209656261/50000000000000 : ℝ)^3907 := by
    have hnat : (4089213761 : ℕ)^4931*50000000000000^3907 ≤ 16174209656261^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4089213761 10000000000 16174209656261 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3083365887/10000000000 : ℝ)^4931 ≤ (22651750150941/100000000000000 : ℝ)^3907 := by
    have hnat : (3083365887 : ℕ)^4931*100000000000000^3907 ≤ 22651750150941^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3083365887 10000000000 22651750150941 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531162143/1000000000 : ℝ)^4931 ≤ (44999830529677/100000000000000 : ℝ)^3907 := by
    have hnat : (531162143 : ℕ)^4931*100000000000000^3907 ≤ 44999830529677^3907*1000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531162143 1000000000 44999830529677 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4089213761/10000000000 : ℝ), (3083365887/10000000000 : ℝ), (531162143/1000000000 : ℝ)] ![(16174209656261/50000000000000 : ℝ), (22651750150941/100000000000000 : ℝ), (44999830529677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4089213761/10000000000 : ℝ)|^4931 ≤ (16174209656261/50000000000000 : ℝ)^3907
        have hw : |(4089213761/10000000000 : ℝ)|=(4089213761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3083365887/10000000000 : ℝ)|^4931 ≤ (22651750150941/100000000000000 : ℝ)^3907
        have hw : |(3083365887/10000000000 : ℝ)|=(3083365887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531162143/1000000000 : ℝ)|^4931 ≤ (44999830529677/100000000000000 : ℝ)^3907
        have hw : |(531162143/1000000000 : ℝ)|=(531162143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s0_4 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-744834579/5000000000 : ℝ)*x 0 + (2472420321/5000000000 : ℝ)*x 1 + (5759611033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (744834579/5000000000 : ℝ)^4931 ≤ (9044027983327/100000000000000 : ℝ)^3907 := by
    have hnat : (744834579 : ℕ)^4931*100000000000000^3907 ≤ 9044027983327^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744834579 5000000000 9044027983327 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2472420321/5000000000 : ℝ)^4931 ≤ (8222834458831/20000000000000 : ℝ)^3907 := by
    have hnat : (2472420321 : ℕ)^4931*20000000000000^3907 ≤ 8222834458831^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2472420321 5000000000 8222834458831 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5759611033/10000000000 : ℝ)^4931 ≤ (9968359942859/20000000000000 : ℝ)^3907 := by
    have hnat : (5759611033 : ℕ)^4931*20000000000000^3907 ≤ 9968359942859^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5759611033 10000000000 9968359942859 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-744834579/5000000000 : ℝ), (2472420321/5000000000 : ℝ), (5759611033/10000000000 : ℝ)] ![(9044027983327/100000000000000 : ℝ), (8222834458831/20000000000000 : ℝ), (9968359942859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-744834579/5000000000 : ℝ)|^4931 ≤ (9044027983327/100000000000000 : ℝ)^3907
        have hw : |(-744834579/5000000000 : ℝ)|=(744834579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2472420321/5000000000 : ℝ)|^4931 ≤ (8222834458831/20000000000000 : ℝ)^3907
        have hw : |(2472420321/5000000000 : ℝ)|=(2472420321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5759611033/10000000000 : ℝ)|^4931 ≤ (9968359942859/20000000000000 : ℝ)^3907
        have hw : |(5759611033/10000000000 : ℝ)|=(5759611033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s0_5 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2601121397/5000000000 : ℝ)*x 0 + (-1122082209/10000000000 : ℝ)*x 1 + (1151921947/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2601121397/5000000000 : ℝ)^4931 ≤ (2191674106373/5000000000000 : ℝ)^3907 := by
    have hnat : (2601121397 : ℕ)^4931*5000000000000^3907 ≤ 2191674106373^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601121397 5000000000 2191674106373 5000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122082209/10000000000 : ℝ)^4931 ≤ (1581183081021/25000000000000 : ℝ)^3907 := by
    have hnat : (1122082209 : ℕ)^4931*25000000000000^3907 ≤ 1581183081021^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122082209 10000000000 1581183081021 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1151921947/2000000000 : ℝ)^4931 ≤ (24920892768933/50000000000000 : ℝ)^3907 := by
    have hnat : (1151921947 : ℕ)^4931*50000000000000^3907 ≤ 24920892768933^3907*2000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1151921947 2000000000 24920892768933 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2601121397/5000000000 : ℝ), (-1122082209/10000000000 : ℝ), (1151921947/2000000000 : ℝ)] ![(2191674106373/5000000000000 : ℝ), (1581183081021/25000000000000 : ℝ), (24920892768933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2601121397/5000000000 : ℝ)|^4931 ≤ (2191674106373/5000000000000 : ℝ)^3907
        have hw : |(2601121397/5000000000 : ℝ)|=(2601121397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1122082209/10000000000 : ℝ)|^4931 ≤ (1581183081021/25000000000000 : ℝ)^3907
        have hw : |(-1122082209/10000000000 : ℝ)|=(1122082209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1151921947/2000000000 : ℝ)|^4931 ≤ (24920892768933/50000000000000 : ℝ)^3907
        have hw : |(1151921947/2000000000 : ℝ)|=(1151921947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s0_6 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5202241999/10000000000 : ℝ)*x 0 + (575961041/1000000000 : ℝ)*x 1 + (-28052059/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202241999/10000000000 : ℝ)^4931 ≤ (4383347367323/10000000000000 : ℝ)^3907 := by
    have hnat : (5202241999 : ℕ)^4931*10000000000000^3907 ≤ 4383347367323^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202241999 10000000000 4383347367323 10000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (575961041/1000000000 : ℝ)^4931 ≤ (24920896455023/50000000000000 : ℝ)^3907 := by
    have hnat : (575961041 : ℕ)^4931*50000000000000^3907 ≤ 24920896455023^3907*1000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575961041 1000000000 24920896455023 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28052059/250000000 : ℝ)^4931 ≤ (3162366699143/50000000000000 : ℝ)^3907 := by
    have hnat : (28052059 : ℕ)^4931*50000000000000^3907 ≤ 3162366699143^3907*250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28052059 250000000 3162366699143 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202241999/10000000000 : ℝ), (575961041/1000000000 : ℝ), (-28052059/250000000 : ℝ)] ![(4383347367323/10000000000000 : ℝ), (24920896455023/50000000000000 : ℝ), (3162366699143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202241999/10000000000 : ℝ)|^4931 ≤ (4383347367323/10000000000000 : ℝ)^3907
        have hw : |(5202241999/10000000000 : ℝ)|=(5202241999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(575961041/1000000000 : ℝ)|^4931 ≤ (24920896455023/50000000000000 : ℝ)^3907
        have hw : |(575961041/1000000000 : ℝ)|=(575961041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28052059/250000000 : ℝ)|^4931 ≤ (3162366699143/50000000000000 : ℝ)^3907
        have hw : |(-28052059/250000000 : ℝ)|=(28052059/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s0_7 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (40950883/100000000 : ℝ)*x 0 + (5256437449/10000000000 : ℝ)*x 1 + (1570226373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40950883/100000000 : ℝ)^4931 ≤ (32407081784153/100000000000000 : ℝ)^3907 := by
    have hnat : (40950883 : ℕ)^4931*100000000000000^3907 ≤ 32407081784153^3907*100000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40950883 100000000 32407081784153 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256437449/10000000000 : ℝ)^4931 ≤ (2775661657603/6250000000000 : ℝ)^3907 := by
    have hnat : (5256437449 : ℕ)^4931*6250000000000^3907 ≤ 2775661657603^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256437449 10000000000 2775661657603 6250000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1570226373/5000000000 : ℝ)^4931 ≤ (23182331678657/100000000000000 : ℝ)^3907 := by
    have hnat : (1570226373 : ℕ)^4931*100000000000000^3907 ≤ 23182331678657^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570226373 5000000000 23182331678657 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(40950883/100000000 : ℝ), (5256437449/10000000000 : ℝ), (1570226373/5000000000 : ℝ)] ![(32407081784153/100000000000000 : ℝ), (2775661657603/6250000000000 : ℝ), (23182331678657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(40950883/100000000 : ℝ)|^4931 ≤ (32407081784153/100000000000000 : ℝ)^3907
        have hw : |(40950883/100000000 : ℝ)|=(40950883/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256437449/10000000000 : ℝ)|^4931 ≤ (2775661657603/6250000000000 : ℝ)^3907
        have hw : |(5256437449/10000000000 : ℝ)|=(5256437449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1570226373/5000000000 : ℝ)|^4931 ≤ (23182331678657/100000000000000 : ℝ)^3907
        have hw : |(1570226373/5000000000 : ℝ)|=(1570226373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1653_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2451/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23293/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4927/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4927 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4927*1^1024 ≤ 0^1024*1^4927 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4927 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4927/1024 : ℝ) ≤ (608516454066216029/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4927 ≤ (608516454066216029/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4927*50000000000000000000^1024 ≤ 608516454066216029^1024*5^4927 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 608516454066216029 50000000000000000000 4927 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (608516454066216029/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4927 := by
      have hnat : (1 : ℕ)^1024*1^4927 ≤ 1^4927*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50608516454066216029/50000000000000000000 : ℝ) ≤ (5012586538979537/5000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (50608516454066216029/50000000000000000000 : ℝ)^1024 ≤ (5012586538979537/5000000000000000 : ℝ)^4927 := by
      have hnat : (50608516454066216029 : ℕ)^1024*5000000000000000^4927 ≤ 5012586538979537^4927*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50608516454066216029 50000000000000000000 5012586538979537 5000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012586538979537/5000000000000000 : ℝ)) (X := (50608516454066216029/50000000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25608516454066216029/25000000000000000000 : ℝ) ≤ (2512586538979537/2500000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (25608516454066216029/25000000000000000000 : ℝ)^1024 ≤ (2512586538979537/2500000000000000 : ℝ)^4927 := by
      have hnat : (25608516454066216029 : ℕ)^1024*2500000000000000^4927 ≤ 2512586538979537^4927*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25608516454066216029 25000000000000000000 2512586538979537 2500000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2512586538979537/2500000000000000 : ℝ)) (X := (25608516454066216029/25000000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12586538979537/2000000000000000 : ℝ)*(0 : ℝ))^(4927/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12586538979537/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(608516454066216029/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12586538979537/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4927/1024 : ℝ) := by
    rw [show (1 : ℝ)+(12586538979537/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5012586538979537/5000000000000000 : ℝ) by norm_num, show 1+(608516454066216029/50000000000000000000 : ℝ)+(0 : ℝ)=(50608516454066216029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(608516454066216029/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12586538979537/2000000000000000 : ℝ)*(2/5 : ℝ))^(4927/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12586538979537/2000000000000000 : ℝ)*(2/5 : ℝ)=(2512586538979537/2500000000000000 : ℝ) by norm_num, show 1+2*(608516454066216029/50000000000000000000 : ℝ)=(25608516454066216029/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12586538979537/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12586538979537/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12586538979537/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12586538979537/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12586538979537/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12586538979537/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-371851657/2500000000 : ℝ)*X 0 0+(289079599/500000000 : ℝ)*X 0 1+(4923591513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5436348911/10000000000 : ℝ)*X 1 0+(-489525139/2500000000 : ℝ)*X 1 1+(4923591969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((543634973/1000000000 : ℝ)*X 2 0+(196943653/400000000 : ℝ)*X 2 1+(-979050153/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4089213761/10000000000 : ℝ)*X 0 0+(3083365887/10000000000 : ℝ)*X 0 1+(531162143/1000000000 : ℝ)*X 0 2+(4089213761/10000000000 : ℝ)*X 1 0+(3083365887/10000000000 : ℝ)*X 1 1+(531162143/1000000000 : ℝ)*X 1 2+(4089213761/10000000000 : ℝ)*X 2 0+(3083365887/10000000000 : ℝ)*X 2 1+(531162143/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-744834579/5000000000 : ℝ)*X 0 0+(2472420321/5000000000 : ℝ)*X 0 1+(5759611033/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2601121397/5000000000 : ℝ)*X 1 0+(-1122082209/10000000000 : ℝ)*X 1 1+(1151921947/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5202241999/10000000000 : ℝ)*X 2 0+(575961041/1000000000 : ℝ)*X 2 1+(-28052059/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((40950883/100000000 : ℝ)*X 0 0+(5256437449/10000000000 : ℝ)*X 0 1+(1570226373/5000000000 : ℝ)*X 0 2+(40950883/100000000 : ℝ)*X 1 0+(5256437449/10000000000 : ℝ)*X 1 1+(1570226373/5000000000 : ℝ)*X 1 2+(40950883/100000000 : ℝ)*X 2 0+(5256437449/10000000000 : ℝ)*X 2 1+(1570226373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40969425297020909873439/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112265403/100000000000000 : ℝ)*(base1) + (189172627/25000000000000 : ℝ)*(base19) + (14566829/1562500000000 : ℝ)*(base23) + (28075939/100000000000000 : ℝ)*(upper3) + (157401867/100000000000000 : ℝ)*(upper5) + (80714597606549/10000000000000 : ℝ)*(major0) + (80714597606549/10000000000000 : ℝ)*(major1) + (80714597606549/10000000000000 : ℝ)*(major2) + (291375802007443/25000000000000 : ℝ)*(sp0) + (1165506572506997/100000000000000 : ℝ)*(sp1) + (1165506396920449/100000000000000 : ℝ)*(sp2) + (224391541237819/50000000000000 : ℝ)*(sp3) + (264589571/6250000000000 : ℝ)*(sp4) + (645813839/50000000000000 : ℝ)*(sp7) + (224392243184359/50000000000000 : ℝ)*(f.failure) + (233101465839501/20000000000000 : ℝ)*(f.sum) + (8589647952187/10000000000000000000000000000 : ℝ)*base66 + (87179235812187/20000000000000000000000000000 : ℝ)*base68 + (15186275147813/20000000000000000000000000000 : ℝ)*base69 + (20599955512187/20000000000000000000000000000 : ℝ)*base72 + (40989751772187/10000000000000000000000000000 : ℝ)*base74 + (11554423767813/20000000000000000000000000000 : ℝ)*base75 + (22035925572187/20000000000000000000000000000 : ℝ)*base78 + (74165503127813/20000000000000000000000000000 : ℝ)*base79 + (14894400847813/10000000000000000000000000000 : ℝ)*base81 + (32115857/5000000000000000000000 : ℝ)*base90 + (32115857/5000000000000000000000 : ℝ)*base92 + (32115857/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107901396465926896041507/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (777463909/100000000000000 : ℝ)*(base19) + (584723249/100000000000000 : ℝ)*(base23) + (11016997/50000000000000 : ℝ)*(base32) + (37266749/50000000000000 : ℝ)*(upper3) + (20770881/50000000000000 : ℝ)*(upper5) + (169993242313937/20000000000000 : ℝ)*(major0) + (169993242313937/20000000000000 : ℝ)*(major1) + (169993242313937/20000000000000 : ℝ)*(major2) + (1146302497/100000000000000 : ℝ)*(sp1) + (1031178413/100000000000000 : ℝ)*(sp2) + (1227339105257611/100000000000000 : ℝ)*(sp4) + (306834295372801/25000000000000 : ℝ)*(sp5) + (1227337489355949/100000000000000 : ℝ)*(sp6) + (472593116012099/100000000000000 : ℝ)*(sp7) + (472593138046093/100000000000000 : ℝ)*(f.failure) + (1227339105257611/100000000000000 : ℝ)*(f.sum) + (36138969667169/20000000000000000000000000000 : ℝ)*base65 + (452356295612831/40000000000000000000000000000 : ℝ)*base68 + (133287267772831/40000000000000000000000000000 : ℝ)*base70 + (21393684812831/40000000000000000000000000000 : ℝ)*base72 + (111471776752831/20000000000000000000000000000 : ℝ)*base74 + (105660917427169/40000000000000000000000000000 : ℝ)*base75 + (142064316732831/40000000000000000000000000000 : ℝ)*base78 + (295447097732831/40000000000000000000000000000 : ℝ)*base80 + (72498176187169/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (24738661/10000000000000000000000 : ℝ)*base89 + (24738661/10000000000000000000000 : ℝ)*base91 + (24738661/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1653_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2451/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23293/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1653_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1653_s1_0 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1592053061/10000000000 : ℝ)*x 0 + (5494035861/10000000000 : ℝ)*x 1 + (2571552417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1592053061/10000000000 : ℝ)^4931 ≤ (1229435267351/12500000000000 : ℝ)^3907 := by
    have hnat : (1592053061 : ℕ)^4931*12500000000000^3907 ≤ 1229435267351^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592053061 10000000000 1229435267351 12500000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5494035861/10000000000 : ℝ)^4931 ≤ (5869873023651/12500000000000 : ℝ)^3907 := by
    have hnat : (5494035861 : ℕ)^4931*12500000000000^3907 ≤ 5869873023651^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494035861 10000000000 5869873023651 12500000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2571552417/5000000000 : ℝ)^4931 ≤ (8641106730861/20000000000000 : ℝ)^3907 := by
    have hnat : (2571552417 : ℕ)^4931*20000000000000^3907 ≤ 8641106730861^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571552417 5000000000 8641106730861 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1592053061/10000000000 : ℝ), (5494035861/10000000000 : ℝ), (2571552417/5000000000 : ℝ)] ![(1229435267351/12500000000000 : ℝ), (5869873023651/12500000000000 : ℝ), (8641106730861/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1592053061/10000000000 : ℝ)|^4931 ≤ (1229435267351/12500000000000 : ℝ)^3907
        have hw : |(-1592053061/10000000000 : ℝ)|=(1592053061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5494035861/10000000000 : ℝ)|^4931 ≤ (5869873023651/12500000000000 : ℝ)^3907
        have hw : |(5494035861/10000000000 : ℝ)|=(5494035861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2571552417/5000000000 : ℝ)|^4931 ≤ (8641106730861/20000000000000 : ℝ)^3907
        have hw : |(2571552417/5000000000 : ℝ)|=(2571552417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s1_1 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679931477/5000000000 : ℝ)*x 0 + (-44360597/250000000 : ℝ)*x 1 + (321444043/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679931477/5000000000 : ℝ)^4931 ≤ (22758130474717/50000000000000 : ℝ)^3907 := by
    have hnat : (2679931477 : ℕ)^4931*50000000000000^3907 ≤ 22758130474717^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679931477 5000000000 22758130474717 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44360597/250000000 : ℝ)^4931 ≤ (1409775865991/12500000000000 : ℝ)^3907 := by
    have hnat : (44360597 : ℕ)^4931*12500000000000^3907 ≤ 1409775865991^3907*250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44360597 250000000 1409775865991 12500000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321444043/625000000 : ℝ)^4931 ≤ (864110642127/2000000000000 : ℝ)^3907 := by
    have hnat : (321444043 : ℕ)^4931*2000000000000^3907 ≤ 864110642127^3907*625000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321444043 625000000 864110642127 2000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679931477/5000000000 : ℝ), (-44360597/250000000 : ℝ), (321444043/625000000 : ℝ)] ![(22758130474717/50000000000000 : ℝ), (1409775865991/12500000000000 : ℝ), (864110642127/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679931477/5000000000 : ℝ)|^4931 ≤ (22758130474717/50000000000000 : ℝ)^3907
        have hw : |(2679931477/5000000000 : ℝ)|=(2679931477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44360597/250000000 : ℝ)|^4931 ≤ (1409775865991/12500000000000 : ℝ)^3907
        have hw : |(-44360597/250000000 : ℝ)|=(44360597/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(321444043/625000000 : ℝ)|^4931 ≤ (864110642127/2000000000000 : ℝ)^3907
        have hw : |(321444043/625000000 : ℝ)|=(321444043/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s1_2 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535986241/1000000000 : ℝ)*x 0 + (2571552639/5000000000 : ℝ)*x 1 + (-443605957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535986241/1000000000 : ℝ)^4931 ≤ (45516255118967/100000000000000 : ℝ)^3907 := by
    have hnat : (535986241 : ℕ)^4931*100000000000000^3907 ≤ 45516255118967^3907*1000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535986241 1000000000 45516255118967 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571552639/5000000000 : ℝ)^4931 ≤ (21602769180893/50000000000000 : ℝ)^3907 := by
    have hnat : (2571552639 : ℕ)^4931*50000000000000^3907 ≤ 21602769180893^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571552639 5000000000 21602769180893 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443605957/2500000000 : ℝ)^4931 ≤ (1409775813849/12500000000000 : ℝ)^3907 := by
    have hnat : (443605957 : ℕ)^4931*12500000000000^3907 ≤ 1409775813849^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443605957 2500000000 1409775813849 12500000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535986241/1000000000 : ℝ), (2571552639/5000000000 : ℝ), (-443605957/2500000000 : ℝ)] ![(45516255118967/100000000000000 : ℝ), (21602769180893/50000000000000 : ℝ), (1409775813849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535986241/1000000000 : ℝ)|^4931 ≤ (45516255118967/100000000000000 : ℝ)^3907
        have hw : |(535986241/1000000000 : ℝ)|=(535986241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2571552639/5000000000 : ℝ)|^4931 ≤ (21602769180893/50000000000000 : ℝ)^3907
        have hw : |(2571552639/5000000000 : ℝ)|=(2571552639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-443605957/2500000000 : ℝ)|^4931 ≤ (1409775813849/12500000000000 : ℝ)^3907
        have hw : |(-443605957/2500000000 : ℝ)|=(443605957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s1_3 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042814799/2500000000 : ℝ)*x 0 + (746700833/2000000000 : ℝ)*x 1 + (145152599/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042814799/2500000000 : ℝ)^4931 ≤ (33169704681579/100000000000000 : ℝ)^3907 := by
    have hnat : (1042814799 : ℕ)^4931*100000000000000^3907 ≤ 33169704681579^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042814799 2500000000 33169704681579 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (746700833/2000000000 : ℝ)^4931 ≤ (28838397027611/100000000000000 : ℝ)^3907 := by
    have hnat : (746700833 : ℕ)^4931*100000000000000^3907 ≤ 28838397027611^3907*2000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746700833 2000000000 28838397027611 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145152599/312500000 : ℝ)^4931 ≤ (7598379656293/20000000000000 : ℝ)^3907 := by
    have hnat : (145152599 : ℕ)^4931*20000000000000^3907 ≤ 7598379656293^3907*312500000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145152599 312500000 7598379656293 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042814799/2500000000 : ℝ), (746700833/2000000000 : ℝ), (145152599/312500000 : ℝ)] ![(33169704681579/100000000000000 : ℝ), (28838397027611/100000000000000 : ℝ), (7598379656293/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042814799/2500000000 : ℝ)|^4931 ≤ (33169704681579/100000000000000 : ℝ)^3907
        have hw : |(1042814799/2500000000 : ℝ)|=(1042814799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(746700833/2000000000 : ℝ)|^4931 ≤ (28838397027611/100000000000000 : ℝ)^3907
        have hw : |(746700833/2000000000 : ℝ)|=(746700833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(145152599/312500000 : ℝ)|^4931 ≤ (7598379656293/20000000000000 : ℝ)^3907
        have hw : |(145152599/312500000 : ℝ)|=(145152599/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s1_4 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-796102569/5000000000 : ℝ)*x 0 + (5146649161/10000000000 : ℝ)*x 1 + (274522089/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (796102569/5000000000 : ℝ)^4931 ≤ (9836667903953/100000000000000 : ℝ)^3907 := by
    have hnat : (796102569 : ℕ)^4931*100000000000000^3907 ≤ 9836667903953^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796102569 5000000000 9836667903953 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5146649161/10000000000 : ℝ)^4931 ≤ (43243115541441/100000000000000 : ℝ)^3907 := by
    have hnat : (5146649161 : ℕ)^4931*100000000000000^3907 ≤ 43243115541441^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5146649161 10000000000 43243115541441 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274522089/500000000 : ℝ)^4931 ≤ (4692021654447/10000000000000 : ℝ)^3907 := by
    have hnat : (274522089 : ℕ)^4931*10000000000000^3907 ≤ 4692021654447^3907*500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274522089 500000000 4692021654447 10000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-796102569/5000000000 : ℝ), (5146649161/10000000000 : ℝ), (274522089/500000000 : ℝ)] ![(9836667903953/100000000000000 : ℝ), (43243115541441/100000000000000 : ℝ), (4692021654447/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-796102569/5000000000 : ℝ)|^4931 ≤ (9836667903953/100000000000000 : ℝ)^3907
        have hw : |(-796102569/5000000000 : ℝ)|=(796102569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5146649161/10000000000 : ℝ)|^4931 ≤ (43243115541441/100000000000000 : ℝ)^3907
        have hw : |(5146649161/10000000000 : ℝ)|=(5146649161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274522089/500000000 : ℝ)|^4931 ≤ (4692021654447/10000000000000 : ℝ)^3907
        have hw : |(274522089/500000000 : ℝ)|=(274522089/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s1_5 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266003563/10000000000 : ℝ)*x 0 + (-1427086943/10000000000 : ℝ)*x 1 + (2745220907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266003563/10000000000 : ℝ)^4931 ≤ (22256308000189/50000000000000 : ℝ)^3907 := by
    have hnat : (5266003563 : ℕ)^4931*50000000000000^3907 ≤ 22256308000189^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266003563 10000000000 22256308000189 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1427086943/10000000000 : ℝ)^4931 ≤ (4283583538137/50000000000000 : ℝ)^3907 := by
    have hnat : (1427086943 : ℕ)^4931*50000000000000^3907 ≤ 4283583538137^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1427086943 10000000000 4283583538137 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745220907/5000000000 : ℝ)^4931 ≤ (2346010845559/5000000000000 : ℝ)^3907 := by
    have hnat : (2745220907 : ℕ)^4931*5000000000000^3907 ≤ 2346010845559^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745220907 5000000000 2346010845559 5000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266003563/10000000000 : ℝ), (-1427086943/10000000000 : ℝ), (2745220907/5000000000 : ℝ)] ![(22256308000189/50000000000000 : ℝ), (4283583538137/50000000000000 : ℝ), (2346010845559/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266003563/10000000000 : ℝ)|^4931 ≤ (22256308000189/50000000000000 : ℝ)^3907
        have hw : |(5266003563/10000000000 : ℝ)|=(5266003563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1427086943/10000000000 : ℝ)|^4931 ≤ (4283583538137/50000000000000 : ℝ)^3907
        have hw : |(-1427086943/10000000000 : ℝ)|=(1427086943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745220907/5000000000 : ℝ)|^4931 ≤ (2346010845559/5000000000000 : ℝ)^3907
        have hw : |(2745220907/5000000000 : ℝ)|=(2745220907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s1_6 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266003347/10000000000 : ℝ)*x 0 + (5490442111/10000000000 : ℝ)*x 1 + (-178385853/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266003347/10000000000 : ℝ)^4931 ≤ (22256306848017/50000000000000 : ℝ)^3907 := by
    have hnat : (5266003347 : ℕ)^4931*50000000000000^3907 ≤ 22256306848017^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266003347 10000000000 22256306848017 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490442111/10000000000 : ℝ)^4931 ≤ (46920220114503/100000000000000 : ℝ)^3907 := by
    have hnat : (5490442111 : ℕ)^4931*100000000000000^3907 ≤ 46920220114503^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490442111 10000000000 46920220114503 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (178385853/1250000000 : ℝ)^4931 ≤ (8567166174651/100000000000000 : ℝ)^3907 := by
    have hnat : (178385853 : ℕ)^4931*100000000000000^3907 ≤ 8567166174651^3907*1250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178385853 1250000000 8567166174651 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266003347/10000000000 : ℝ), (5490442111/10000000000 : ℝ), (-178385853/1250000000 : ℝ)] ![(22256306848017/50000000000000 : ℝ), (46920220114503/100000000000000 : ℝ), (8567166174651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266003347/10000000000 : ℝ)|^4931 ≤ (22256306848017/50000000000000 : ℝ)^3907
        have hw : |(5266003347/10000000000 : ℝ)|=(5266003347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490442111/10000000000 : ℝ)|^4931 ≤ (46920220114503/100000000000000 : ℝ)^3907
        have hw : |(5490442111/10000000000 : ℝ)|=(5490442111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-178385853/1250000000 : ℝ)|^4931 ≤ (8567166174651/100000000000000 : ℝ)^3907
        have hw : |(-178385853/1250000000 : ℝ)|=(178385853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s1_7 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042913601/2500000000 : ℝ)*x 0 + (4635678819/10000000000 : ℝ)*x 1 + (935709587/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042913601/2500000000 : ℝ)^4931 ≤ (33173671087323/100000000000000 : ℝ)^3907 := by
    have hnat : (1042913601 : ℕ)^4931*100000000000000^3907 ≤ 33173671087323^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042913601 2500000000 33173671087323 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4635678819/10000000000 : ℝ)^4931 ≤ (473711325819/1250000000000 : ℝ)^3907 := by
    have hnat : (4635678819 : ℕ)^4931*1250000000000^3907 ≤ 473711325819^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4635678819 10000000000 473711325819 1250000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (935709587/2500000000 : ℝ)^4931 ≤ (14464711419301/50000000000000 : ℝ)^3907 := by
    have hnat : (935709587 : ℕ)^4931*50000000000000^3907 ≤ 14464711419301^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935709587 2500000000 14464711419301 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042913601/2500000000 : ℝ), (4635678819/10000000000 : ℝ), (935709587/2500000000 : ℝ)] ![(33173671087323/100000000000000 : ℝ), (473711325819/1250000000000 : ℝ), (14464711419301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042913601/2500000000 : ℝ)|^4931 ≤ (33173671087323/100000000000000 : ℝ)^3907
        have hw : |(1042913601/2500000000 : ℝ)|=(1042913601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4635678819/10000000000 : ℝ)|^4931 ≤ (473711325819/1250000000000 : ℝ)^3907
        have hw : |(4635678819/10000000000 : ℝ)|=(4635678819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(935709587/2500000000 : ℝ)|^4931 ≤ (14464711419301/50000000000000 : ℝ)^3907
        have hw : |(935709587/2500000000 : ℝ)|=(935709587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1653_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23293/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2451/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4899/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3451/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23293/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2451/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23293/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2451/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23293/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2451/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23293/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2451/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23293/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2451/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23293/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2451/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2451/50000 : ℝ) ^ (4927/1024 : ℝ) ≤ (2498448927659/5000000000000000000 : ℝ) := by
    have hpowers : (2451/50000 : ℝ)^4927 ≤ (2498448927659/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2451 : ℕ)^4927*5000000000000000000^1024 ≤ 2498448927659^1024*50000^4927 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2451 50000 2498448927659 5000000000000000000 4927 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2451/50000 : ℝ)) (X := (2498448927659/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23293/100000 : ℝ) ^ (4927/1024 : ℝ) ≤ (90238176329744987/100000000000000000000 : ℝ) := by
    have hpowers : (23293/100000 : ℝ)^4927 ≤ (90238176329744987/100000000000000000000 : ℝ)^1024 := by
      have hnat : (23293 : ℕ)^4927*100000000000000000000^1024 ≤ 90238176329744987^1024*100000^4927 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23293 100000 90238176329744987 100000000000000000000 4927 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23293/100000 : ℝ)) (X := (90238176329744987/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500002498448927659/2500000000000000000 : ℝ) ≤ (10000002077053533/10000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (2500002498448927659/2500000000000000000 : ℝ)^1024 ≤ (10000002077053533/10000000000000000 : ℝ)^4927 := by
      have hnat : (2500002498448927659 : ℕ)^1024*10000000000000000^4927 ≤ 10000002077053533^4927*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500002498448927659 2500000000000000000 10000002077053533 10000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002077053533/10000000000000000 : ℝ)) (X := (2500002498448927659/2500000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100090288145308298167/100000000000000000000 : ℝ) ≤ (5000937913692159/5000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (100090288145308298167/100000000000000000000 : ℝ)^1024 ≤ (5000937913692159/5000000000000000 : ℝ)^4927 := by
      have hnat : (100090288145308298167 : ℕ)^1024*5000000000000000^4927 ≤ 5000937913692159^4927*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100090288145308298167 100000000000000000000 5000937913692159 5000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000937913692159/5000000000000000 : ℝ)) (X := (100090288145308298167/100000000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50090238176329744987/50000000000000000000 : ℝ) ≤ (10003749577715103/10000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (50090238176329744987/50000000000000000000 : ℝ)^1024 ≤ (10003749577715103/10000000000000000 : ℝ)^4927 := by
      have hnat : (50090238176329744987 : ℕ)^1024*10000000000000000^4927 ≤ 10003749577715103^4927*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50090238176329744987 50000000000000000000 10003749577715103 10000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003749577715103/10000000000000000 : ℝ)) (X := (50090238176329744987/50000000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2498448927659/5000000000000000000 : ℝ) ≤ ((183891667950848509263/183910000000000000000 : ℝ)+2*(374750066157/367820000000000 : ℝ)*(2451/50000 : ℝ))^(4927/1024 : ℝ) := by
    rw [show (183891667950848509263/183910000000000000000 : ℝ)+2*(374750066157/367820000000000 : ℝ)*(2451/50000 : ℝ)=(10000002077053533/10000000000000000 : ℝ) by norm_num, show 1+2*(2498448927659/5000000000000000000 : ℝ)=(2500002498448927659/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(90238176329744987/100000000000000000000 : ℝ)+(2498448927659/5000000000000000000 : ℝ) ≤ ((183891667950848509263/183910000000000000000 : ℝ)+(374750066157/367820000000000 : ℝ)*((23293/100000 : ℝ)+(2451/50000 : ℝ)))^(4927/1024 : ℝ) := by
    rw [show (183891667950848509263/183910000000000000000 : ℝ)+(374750066157/367820000000000 : ℝ)*((23293/100000 : ℝ)+(2451/50000 : ℝ))=(5000937913692159/5000000000000000 : ℝ) by norm_num, show 1+(90238176329744987/100000000000000000000 : ℝ)+(2498448927659/5000000000000000000 : ℝ)=(100090288145308298167/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(90238176329744987/100000000000000000000 : ℝ) ≤ ((183891667950848509263/183910000000000000000 : ℝ)+2*(374750066157/367820000000000 : ℝ)*(23293/100000 : ℝ))^(4927/1024 : ℝ) := by
    rw [show (183891667950848509263/183910000000000000000 : ℝ)+2*(374750066157/367820000000000 : ℝ)*(23293/100000 : ℝ)=(10003749577715103/10000000000000000 : ℝ) by norm_num, show 1+2*(90238176329744987/100000000000000000000 : ℝ)=(50090238176329744987/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (183891667950848509263/183910000000000000000 : ℝ)*(X 1 0+X 2 0)+(374750066157/367820000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (2451/50000 : ℝ)) (hi := (23293/100000 : ℝ)) (c := (183891667950848509263/183910000000000000000 : ℝ)) (alpha := (374750066157/367820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (183891667950848509263/183910000000000000000 : ℝ)*(X 0 1+X 2 1)+(374750066157/367820000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (2451/50000 : ℝ)) (hi := (23293/100000 : ℝ)) (c := (183891667950848509263/183910000000000000000 : ℝ)) (alpha := (374750066157/367820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (183891667950848509263/183910000000000000000 : ℝ)*(X 0 2+X 1 2)+(374750066157/367820000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (2451/50000 : ℝ)) (hi := (23293/100000 : ℝ)) (c := (183891667950848509263/183910000000000000000 : ℝ)) (alpha := (374750066157/367820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1592053061/10000000000 : ℝ)*X 0 0+(5494035861/10000000000 : ℝ)*X 0 1+(2571552417/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2679931477/5000000000 : ℝ)*X 1 0+(-44360597/250000000 : ℝ)*X 1 1+(321444043/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535986241/1000000000 : ℝ)*X 2 0+(2571552639/5000000000 : ℝ)*X 2 1+(-443605957/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1042814799/2500000000 : ℝ)*X 0 0+(746700833/2000000000 : ℝ)*X 0 1+(145152599/312500000 : ℝ)*X 0 2+(1042814799/2500000000 : ℝ)*X 1 0+(746700833/2000000000 : ℝ)*X 1 1+(145152599/312500000 : ℝ)*X 1 2+(1042814799/2500000000 : ℝ)*X 2 0+(746700833/2000000000 : ℝ)*X 2 1+(145152599/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-796102569/5000000000 : ℝ)*X 0 0+(5146649161/10000000000 : ℝ)*X 0 1+(274522089/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5266003563/10000000000 : ℝ)*X 1 0+(-1427086943/10000000000 : ℝ)*X 1 1+(2745220907/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5266003347/10000000000 : ℝ)*X 2 0+(5490442111/10000000000 : ℝ)*X 2 1+(-178385853/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1042913601/2500000000 : ℝ)*X 0 0+(4635678819/10000000000 : ℝ)*X 0 1+(935709587/2500000000 : ℝ)*X 0 2+(1042913601/2500000000 : ℝ)*X 1 0+(4635678819/10000000000 : ℝ)*X 1 1+(935709587/2500000000 : ℝ)*X 1 2+(1042913601/2500000000 : ℝ)*X 2 0+(4635678819/10000000000 : ℝ)*X 2 1+(935709587/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92952358264089641393307/18391000000000000000000000000 : ℝ) := by norm_num
    linear_combination (725539931/50000000000000 : ℝ)*(base19) + (1038781207/100000000000000 : ℝ)*(base23) + (56715129/25000000000000 : ℝ)*(upper3) + (32984407/50000000000000 : ℝ)*(upper4) + (32239299/25000000000000 : ℝ)*(upper5) + (1973419249624283/100000000000000 : ℝ)*(major0) + (1973419249624283/100000000000000 : ℝ)*(major1) + (1973419249624283/100000000000000 : ℝ)*(major2) + (569915396152447/20000000000000 : ℝ)*(sp0) + (2849588091253473/100000000000000 : ℝ)*(sp1) + (22262410184001/781250000000 : ℝ)*(sp2) + (877794639947/80000000000 : ℝ)*(sp3) + (12561571101/100000000000000 : ℝ)*(sp4) + (5488507111/100000000000000 : ℝ)*(sp7) + (1097248788440861/100000000000000 : ℝ)*(f.failure) + (356198692791667/12500000000000 : ℝ)*(f.sum) + (4491040935617/1839100000000000000000000000 : ℝ)*base65 + (74577427977094266571/18391000000000000000000000000000000 : ℝ)*base68 + (56019072507007266571/18391000000000000000000000000000000 : ℝ)*base70 + (166502561865984733429/18391000000000000000000000000000000 : ℝ)*base71 + (9018263309801/9195500000000000000000000000 : ℝ)*base73 + (11484119401721266571/18391000000000000000000000000000000 : ℝ)*base76 + (148365923409926733429/18391000000000000000000000000000000 : ℝ)*base77 + (159780446177597733429/18391000000000000000000000000000000 : ℝ)*base79 + (17488636200627/18391000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (77912203/10000000000000000000000 : ℝ)*base90 + (77912203/10000000000000000000000 : ℝ)*base92 + (77912203/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9539912519710052060279106711/4597750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (544218021/100000000000000 : ℝ)*(base19) + (560955361/100000000000000 : ℝ)*(base23) + (54695923/100000000000000 : ℝ)*(upper2) + (6775727/10000000000000 : ℝ)*(upper3) + (29167697/50000000000000 : ℝ)*(upper5) + (2014374947660499/100000000000000 : ℝ)*(major0) + (2014374947660499/100000000000000 : ℝ)*(major1) + (2014374947660499/100000000000000 : ℝ)*(major2) + (5399673051/100000000000000 : ℝ)*(sp1) + (7205218391/100000000000000 : ℝ)*(sp2) + (1454364547514721/50000000000000 : ℝ)*(sp4) + (290872315113837/10000000000000 : ℝ)*(sp5) + (290872132885569/10000000000000 : ℝ)*(sp6) + (1120020731127923/100000000000000 : ℝ)*(sp7) + (1120020731127923/100000000000000 : ℝ)*(f.failure) + (1454364547514721/50000000000000 : ℝ)*(f.sum) + (27171222604993/18391000000000000000000000000 : ℝ)*base66 + (6552901931956797763/18391000000000000000000000000000000 : ℝ)*base68 + (40124143496171797763/18391000000000000000000000000000000 : ℝ)*base70 + (51576401119943797763/18391000000000000000000000000000000 : ℝ)*base72 + (29874599873433/9195500000000000000000000000 : ℝ)*base73 + (75550349927799797763/18391000000000000000000000000000000 : ℝ)*base76 + (1709421192359797763/18391000000000000000000000000000000 : ℝ)*base78 + (16010443529777202237/18391000000000000000000000000000000 : ℝ)*base79 + (32885159176993/18391000000000000000000000000 : ℝ)*base82 + (40284571/10000000000000000000000 : ℝ)*base89 + (40284571/10000000000000000000000 : ℝ)*base91 + (40284571/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1653_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23293/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2451/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4899/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3451/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1653_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1653_s2_0 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1601073937/10000000000 : ℝ)*x 0 + (5450023123/10000000000 : ℝ)*x 1 + (2590581393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1601073937/10000000000 : ℝ)^4931 ≤ (990587041543/10000000000000 : ℝ)^3907 := by
    have hnat : (1601073937 : ℕ)^4931*10000000000000^3907 ≤ 990587041543^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1601073937 10000000000 990587041543 10000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450023123/10000000000 : ℝ)^4931 ≤ (46484698402281/100000000000000 : ℝ)^3907 := by
    have hnat : (5450023123 : ℕ)^4931*100000000000000^3907 ≤ 46484698402281^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450023123 10000000000 46484698402281 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590581393/5000000000 : ℝ)^4931 ≤ (43609431167391/100000000000000 : ℝ)^3907 := by
    have hnat : (2590581393 : ℕ)^4931*100000000000000^3907 ≤ 43609431167391^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590581393 5000000000 43609431167391 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1601073937/10000000000 : ℝ), (5450023123/10000000000 : ℝ), (2590581393/5000000000 : ℝ)] ![(990587041543/10000000000000 : ℝ), (46484698402281/100000000000000 : ℝ), (43609431167391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1601073937/10000000000 : ℝ)|^4931 ≤ (990587041543/10000000000000 : ℝ)^3907
        have hw : |(-1601073937/10000000000 : ℝ)|=(1601073937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450023123/10000000000 : ℝ)|^4931 ≤ (46484698402281/100000000000000 : ℝ)^3907
        have hw : |(5450023123/10000000000 : ℝ)|=(5450023123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590581393/5000000000 : ℝ)|^4931 ≤ (43609431167391/100000000000000 : ℝ)^3907
        have hw : |(2590581393/5000000000 : ℝ)|=(2590581393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s2_1 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674100721/5000000000 : ℝ)*x 0 + (-347911769/2000000000 : ℝ)*x 1 + (5181163629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674100721/5000000000 : ℝ)^4931 ≤ (22695655593033/50000000000000 : ℝ)^3907 := by
    have hnat : (2674100721 : ℕ)^4931*50000000000000^3907 ≤ 22695655593033^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674100721 5000000000 22695655593033 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (347911769/2000000000 : ℝ)^4931 ≤ (10999248676339/100000000000000 : ℝ)^3907 := by
    have hnat : (347911769 : ℕ)^4931*100000000000000^3907 ≤ 10999248676339^3907*2000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347911769 2000000000 10999248676339 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181163629/10000000000 : ℝ)^4931 ≤ (43609440122531/100000000000000 : ℝ)^3907 := by
    have hnat : (5181163629 : ℕ)^4931*100000000000000^3907 ≤ 43609440122531^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181163629 10000000000 43609440122531 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674100721/5000000000 : ℝ), (-347911769/2000000000 : ℝ), (5181163629/10000000000 : ℝ)] ![(22695655593033/50000000000000 : ℝ), (10999248676339/100000000000000 : ℝ), (43609440122531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674100721/5000000000 : ℝ)|^4931 ≤ (22695655593033/50000000000000 : ℝ)^3907
        have hw : |(2674100721/5000000000 : ℝ)|=(2674100721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-347911769/2000000000 : ℝ)|^4931 ≤ (10999248676339/100000000000000 : ℝ)^3907
        have hw : |(-347911769/2000000000 : ℝ)|=(347911769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181163629/10000000000 : ℝ)|^4931 ≤ (43609440122531/100000000000000 : ℝ)^3907
        have hw : |(5181163629/10000000000 : ℝ)|=(5181163629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s2_2 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674101231/5000000000 : ℝ)*x 0 + (2590581351/5000000000 : ℝ)*x 1 + (-173955871/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674101231/5000000000 : ℝ)^4931 ≤ (22695661055977/50000000000000 : ℝ)^3907 := by
    have hnat : (2674101231 : ℕ)^4931*50000000000000^3907 ≤ 22695661055977^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674101231 5000000000 22695661055977 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590581351/5000000000 : ℝ)^4931 ≤ (5451178784383/12500000000000 : ℝ)^3907 := by
    have hnat : (2590581351 : ℕ)^4931*12500000000000^3907 ≤ 5451178784383^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590581351 5000000000 5451178784383 12500000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173955871/1000000000 : ℝ)^4931 ≤ (343726487469/3125000000000 : ℝ)^3907 := by
    have hnat : (173955871 : ℕ)^4931*3125000000000^3907 ≤ 343726487469^3907*1000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173955871 1000000000 343726487469 3125000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674101231/5000000000 : ℝ), (2590581351/5000000000 : ℝ), (-173955871/1000000000 : ℝ)] ![(22695661055977/50000000000000 : ℝ), (5451178784383/12500000000000 : ℝ), (343726487469/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674101231/5000000000 : ℝ)|^4931 ≤ (22695661055977/50000000000000 : ℝ)^3907
        have hw : |(2674101231/5000000000 : ℝ)|=(2674101231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590581351/5000000000 : ℝ)|^4931 ≤ (5451178784383/12500000000000 : ℝ)^3907
        have hw : |(2590581351/5000000000 : ℝ)|=(2590581351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173955871/1000000000 : ℝ)|^4931 ≤ (343726487469/3125000000000 : ℝ)^3907
        have hw : |(-173955871/1000000000 : ℝ)|=(173955871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s2_3 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4177988633/10000000000 : ℝ)*x 0 + (959850361/2500000000 : ℝ)*x 1 + (28360241/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4177988633/10000000000 : ℝ)^4931 ≤ (16618628209347/50000000000000 : ℝ)^3907 := by
    have hnat : (4177988633 : ℕ)^4931*50000000000000^3907 ≤ 16618628209347^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4177988633 10000000000 16618628209347 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (959850361/2500000000 : ℝ)^4931 ≤ (29874567166253/100000000000000 : ℝ)^3907 := by
    have hnat : (959850361 : ℕ)^4931*100000000000000^3907 ≤ 29874567166253^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959850361 2500000000 29874567166253 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28360241/62500000 : ℝ)^4931 ≤ (36888176395891/100000000000000 : ℝ)^3907 := by
    have hnat : (28360241 : ℕ)^4931*100000000000000^3907 ≤ 36888176395891^3907*62500000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28360241 62500000 36888176395891 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4177988633/10000000000 : ℝ), (959850361/2500000000 : ℝ), (28360241/62500000 : ℝ)] ![(16618628209347/50000000000000 : ℝ), (29874567166253/100000000000000 : ℝ), (36888176395891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4177988633/10000000000 : ℝ)|^4931 ≤ (16618628209347/50000000000000 : ℝ)^3907
        have hw : |(4177988633/10000000000 : ℝ)|=(4177988633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(959850361/2500000000 : ℝ)|^4931 ≤ (29874567166253/100000000000000 : ℝ)^3907
        have hw : |(959850361/2500000000 : ℝ)|=(959850361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28360241/62500000 : ℝ)|^4931 ≤ (36888176395891/100000000000000 : ℝ)^3907
        have hw : |(28360241/62500000 : ℝ)|=(28360241/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s2_4 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1601142561/10000000000 : ℝ)*x 0 + (103664973/200000000 : ℝ)*x 1 + (5447914739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1601142561/10000000000 : ℝ)^4931 ≤ (4953203137699/50000000000000 : ℝ)^3907 := by
    have hnat : (1601142561 : ℕ)^4931*50000000000000^3907 ≤ 4953203137699^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1601142561 10000000000 4953203137699 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103664973/200000000 : ℝ)^4931 ≤ (10907897586701/25000000000000 : ℝ)^3907 := by
    have hnat : (103664973 : ℕ)^4931*25000000000000^3907 ≤ 10907897586701^3907*200000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103664973 200000000 10907897586701 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5447914739/10000000000 : ℝ)^4931 ≤ (5807750420263/12500000000000 : ℝ)^3907 := by
    have hnat : (5447914739 : ℕ)^4931*12500000000000^3907 ≤ 5807750420263^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447914739 10000000000 5807750420263 12500000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1601142561/10000000000 : ℝ), (103664973/200000000 : ℝ), (5447914739/10000000000 : ℝ)] ![(4953203137699/50000000000000 : ℝ), (10907897586701/25000000000000 : ℝ), (5807750420263/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1601142561/10000000000 : ℝ)|^4931 ≤ (4953203137699/50000000000000 : ℝ)^3907
        have hw : |(-1601142561/10000000000 : ℝ)|=(1601142561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103664973/200000000 : ℝ)|^4931 ≤ (10907897586701/25000000000000 : ℝ)^3907
        have hw : |(103664973/200000000 : ℝ)|=(103664973/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5447914739/10000000000 : ℝ)|^4931 ≤ (5807750420263/12500000000000 : ℝ)^3907
        have hw : |(5447914739/10000000000 : ℝ)|=(5447914739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s2_5 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659543261/1250000000 : ℝ)*x 0 + (-184100853/1250000000 : ℝ)*x 1 + (217916593/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659543261/1250000000 : ℝ)^4931 ≤ (11155745280751/25000000000000 : ℝ)^3907 := by
    have hnat : (659543261 : ℕ)^4931*25000000000000^3907 ≤ 11155745280751^3907*1250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659543261 1250000000 11155745280751 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (184100853/1250000000 : ℝ)^4931 ≤ (139297102777/1562500000000 : ℝ)^3907 := by
    have hnat : (184100853 : ℕ)^4931*1562500000000^3907 ≤ 139297102777^3907*1250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184100853 1250000000 139297102777 1562500000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217916593/400000000 : ℝ)^4931 ≤ (46462004287777/100000000000000 : ℝ)^3907 := by
    have hnat : (217916593 : ℕ)^4931*100000000000000^3907 ≤ 46462004287777^3907*400000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217916593 400000000 46462004287777 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659543261/1250000000 : ℝ), (-184100853/1250000000 : ℝ), (217916593/400000000 : ℝ)] ![(11155745280751/25000000000000 : ℝ), (139297102777/1562500000000 : ℝ), (46462004287777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659543261/1250000000 : ℝ)|^4931 ≤ (11155745280751/25000000000000 : ℝ)^3907
        have hw : |(659543261/1250000000 : ℝ)|=(659543261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-184100853/1250000000 : ℝ)|^4931 ≤ (139297102777/1562500000000 : ℝ)^3907
        have hw : |(-184100853/1250000000 : ℝ)|=(184100853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217916593/400000000 : ℝ)|^4931 ≤ (46462004287777/100000000000000 : ℝ)^3907
        have hw : |(217916593/400000000 : ℝ)|=(217916593/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s2_6 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276345651/10000000000 : ℝ)*x 0 + (680989381/1250000000 : ℝ)*x 1 + (-18410089/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276345651/10000000000 : ℝ)^4931 ≤ (44622976458577/100000000000000 : ℝ)^3907 := by
    have hnat : (5276345651 : ℕ)^4931*100000000000000^3907 ≤ 44622976458577^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276345651 10000000000 44622976458577 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680989381/1250000000 : ℝ)^4931 ≤ (46462006688069/100000000000000 : ℝ)^3907 := by
    have hnat : (680989381 : ℕ)^4931*100000000000000^3907 ≤ 46462006688069^3907*1250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680989381 1250000000 46462006688069 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18410089/125000000 : ℝ)^4931 ≤ (1783003367807/20000000000000 : ℝ)^3907 := by
    have hnat : (18410089 : ℕ)^4931*20000000000000^3907 ≤ 1783003367807^3907*125000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18410089 125000000 1783003367807 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276345651/10000000000 : ℝ), (680989381/1250000000 : ℝ), (-18410089/125000000 : ℝ)] ![(44622976458577/100000000000000 : ℝ), (46462006688069/100000000000000 : ℝ), (1783003367807/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276345651/10000000000 : ℝ)|^4931 ≤ (44622976458577/100000000000000 : ℝ)^3907
        have hw : |(5276345651/10000000000 : ℝ)|=(5276345651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680989381/1250000000 : ℝ)|^4931 ≤ (46462006688069/100000000000000 : ℝ)^3907
        have hw : |(680989381/1250000000 : ℝ)|=(680989381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18410089/125000000 : ℝ)|^4931 ≤ (1783003367807/20000000000000 : ℝ)^3907
        have hw : |(-18410089/125000000 : ℝ)|=(18410089/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s2_7 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4178167339/10000000000 : ℝ)*x 0 + (226611063/500000000 : ℝ)*x 1 + (3844876639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4178167339/10000000000 : ℝ)^4931 ≤ (16619525351117/50000000000000 : ℝ)^3907 := by
    have hnat : (4178167339 : ℕ)^4931*50000000000000^3907 ≤ 16619525351117^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4178167339 10000000000 16619525351117 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226611063/500000000 : ℝ)^4931 ≤ (9208150850541/25000000000000 : ℝ)^3907 := by
    have hnat : (226611063 : ℕ)^4931*25000000000000^3907 ≤ 9208150850541^3907*500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226611063 500000000 9208150850541 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3844876639/10000000000 : ℝ)^4931 ≤ (935260808729/3125000000000 : ℝ)^3907 := by
    have hnat : (3844876639 : ℕ)^4931*3125000000000^3907 ≤ 935260808729^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3844876639 10000000000 935260808729 3125000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4178167339/10000000000 : ℝ), (226611063/500000000 : ℝ), (3844876639/10000000000 : ℝ)] ![(16619525351117/50000000000000 : ℝ), (9208150850541/25000000000000 : ℝ), (935260808729/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4178167339/10000000000 : ℝ)|^4931 ≤ (16619525351117/50000000000000 : ℝ)^3907
        have hw : |(4178167339/10000000000 : ℝ)|=(4178167339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226611063/500000000 : ℝ)|^4931 ≤ (9208150850541/25000000000000 : ℝ)^3907
        have hw : |(226611063/500000000 : ℝ)|=(226611063/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3844876639/10000000000 : ℝ)|^4931 ≤ (935260808729/3125000000000 : ℝ)^3907
        have hw : |(3844876639/10000000000 : ℝ)|=(3844876639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1653_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3451/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4899/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (531/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1021/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3451/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4899/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3451/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4899/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3451/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4899/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3451/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4899/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3451/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4899/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3451/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4899/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4899/50000 : ℝ) ^ (4927/1024 : ℝ) ≤ (279810572156797/20000000000000000000 : ℝ) := by
    have hpowers : (4899/50000 : ℝ)^4927 ≤ (279810572156797/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4899 : ℕ)^4927*20000000000000000000^1024 ≤ 279810572156797^1024*50000^4927 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4899 50000 279810572156797 20000000000000000000 4927 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4899/50000 : ℝ)) (X := (279810572156797/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3451/20000 : ℝ) ^ (4927/1024 : ℝ) ≤ (4260184994630347/20000000000000000000 : ℝ) := by
    have hpowers : (3451/20000 : ℝ)^4927 ≤ (4260184994630347/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3451 : ℕ)^4927*20000000000000000000^1024 ≤ 4260184994630347^1024*20000^4927 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3451 20000 4260184994630347 20000000000000000000 4927 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3451/20000 : ℝ)) (X := (4260184994630347/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000279810572156797/10000000000000000000 : ℝ) ≤ (10000058153612833/10000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (10000279810572156797/10000000000000000000 : ℝ)^1024 ≤ (10000058153612833/10000000000000000 : ℝ)^4927 := by
      have hnat : (10000279810572156797 : ℕ)^1024*10000000000000000^4927 ≤ 10000058153612833^4927*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000279810572156797 10000000000000000000 10000058153612833 10000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000058153612833/10000000000000000 : ℝ)) (X := (10000279810572156797/10000000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500567499445848393/2500000000000000000 : ℝ) ≤ (2000094348234751/2000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (2500567499445848393/2500000000000000000 : ℝ)^1024 ≤ (2000094348234751/2000000000000000 : ℝ)^4927 := by
      have hnat : (2500567499445848393 : ℕ)^1024*2000000000000000^4927 ≤ 2000094348234751^4927*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500567499445848393 2500000000000000000 2000094348234751 2000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000094348234751/2000000000000000 : ℝ)) (X := (2500567499445848393/2500000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004260184994630347/10000000000000000000 : ℝ) ≤ (10000885328734677/10000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (10004260184994630347/10000000000000000000 : ℝ)^1024 ≤ (10000885328734677/10000000000000000 : ℝ)^4927 := by
      have hnat : (10004260184994630347 : ℕ)^1024*10000000000000000^4927 ≤ 10000885328734677^4927*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004260184994630347 10000000000000000000 10000885328734677 10000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000885328734677/10000000000000000 : ℝ)) (X := (10004260184994630347/10000000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(279810572156797/20000000000000000000 : ℝ) ≤ ((74562328989647068169/74570000000000000000 : ℝ)+2*(206793780461/372850000000000 : ℝ)*(4899/50000 : ℝ))^(4927/1024 : ℝ) := by
    rw [show (74562328989647068169/74570000000000000000 : ℝ)+2*(206793780461/372850000000000 : ℝ)*(4899/50000 : ℝ)=(10000058153612833/10000000000000000 : ℝ) by norm_num, show 1+2*(279810572156797/20000000000000000000 : ℝ)=(10000279810572156797/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4260184994630347/20000000000000000000 : ℝ)+(279810572156797/20000000000000000000 : ℝ) ≤ ((74562328989647068169/74570000000000000000 : ℝ)+(206793780461/372850000000000 : ℝ)*((3451/20000 : ℝ)+(4899/50000 : ℝ)))^(4927/1024 : ℝ) := by
    rw [show (74562328989647068169/74570000000000000000 : ℝ)+(206793780461/372850000000000 : ℝ)*((3451/20000 : ℝ)+(4899/50000 : ℝ))=(2000094348234751/2000000000000000 : ℝ) by norm_num, show 1+(4260184994630347/20000000000000000000 : ℝ)+(279810572156797/20000000000000000000 : ℝ)=(2500567499445848393/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4260184994630347/20000000000000000000 : ℝ) ≤ ((74562328989647068169/74570000000000000000 : ℝ)+2*(206793780461/372850000000000 : ℝ)*(3451/20000 : ℝ))^(4927/1024 : ℝ) := by
    rw [show (74562328989647068169/74570000000000000000 : ℝ)+2*(206793780461/372850000000000 : ℝ)*(3451/20000 : ℝ)=(10000885328734677/10000000000000000 : ℝ) by norm_num, show 1+2*(4260184994630347/20000000000000000000 : ℝ)=(10004260184994630347/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (74562328989647068169/74570000000000000000 : ℝ)*(X 1 0+X 2 0)+(206793780461/372850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (4899/50000 : ℝ)) (hi := (3451/20000 : ℝ)) (c := (74562328989647068169/74570000000000000000 : ℝ)) (alpha := (206793780461/372850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (74562328989647068169/74570000000000000000 : ℝ)*(X 0 1+X 2 1)+(206793780461/372850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (4899/50000 : ℝ)) (hi := (3451/20000 : ℝ)) (c := (74562328989647068169/74570000000000000000 : ℝ)) (alpha := (206793780461/372850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (74562328989647068169/74570000000000000000 : ℝ)*(X 0 2+X 1 2)+(206793780461/372850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (4899/50000 : ℝ)) (hi := (3451/20000 : ℝ)) (c := (74562328989647068169/74570000000000000000 : ℝ)) (alpha := (206793780461/372850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1601073937/10000000000 : ℝ)*X 0 0+(5450023123/10000000000 : ℝ)*X 0 1+(2590581393/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674100721/5000000000 : ℝ)*X 1 0+(-347911769/2000000000 : ℝ)*X 1 1+(5181163629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674101231/5000000000 : ℝ)*X 2 0+(2590581351/5000000000 : ℝ)*X 2 1+(-173955871/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4177988633/10000000000 : ℝ)*X 0 0+(959850361/2500000000 : ℝ)*X 0 1+(28360241/62500000 : ℝ)*X 0 2+(4177988633/10000000000 : ℝ)*X 1 0+(959850361/2500000000 : ℝ)*X 1 1+(28360241/62500000 : ℝ)*X 1 2+(4177988633/10000000000 : ℝ)*X 2 0+(959850361/2500000000 : ℝ)*X 2 1+(28360241/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1601142561/10000000000 : ℝ)*X 0 0+(103664973/200000000 : ℝ)*X 0 1+(5447914739/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((659543261/1250000000 : ℝ)*X 1 0+(-184100853/1250000000 : ℝ)*X 1 1+(217916593/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276345651/10000000000 : ℝ)*X 2 0+(680989381/1250000000 : ℝ)*X 2 1+(-18410089/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4178167339/10000000000 : ℝ)*X 0 0+(226611063/500000000 : ℝ)*X 0 1+(3844876639/10000000000 : ℝ)*X 0 2+(4178167339/10000000000 : ℝ)*X 1 0+(226611063/500000000 : ℝ)*X 1 1+(3844876639/10000000000 : ℝ)*X 1 2+(4178167339/10000000000 : ℝ)*X 2 0+(226611063/500000000 : ℝ)*X 2 1+(3844876639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9661851944900876442912907119/1864250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (413491021/100000000000000 : ℝ)*(base19) + (881581063/100000000000000 : ℝ)*(base23) + (123706011/100000000000000 : ℝ)*(upper3) + (25807479/20000000000000 : ℝ)*(upper4) + (82808271/50000000000000 : ℝ)*(upper5) + (1287902517203839/50000000000000 : ℝ)*(major0) + (1287902517203839/50000000000000 : ℝ)*(major1) + (1287902517203839/50000000000000 : ℝ)*(major2) + (464926446724807/12500000000000 : ℝ)*(sp0) + (3719425746748769/100000000000000 : ℝ)*(sp1) + (1859712639329363/50000000000000 : ℝ)*(sp2) + (716090157953447/50000000000000 : ℝ)*(sp3) + (7293220667/50000000000000 : ℝ)*(sp4) + (13359031/390625000000 : ℝ)*(sp7) + (1432183735818829/100000000000000 : ℝ)*(f.failure) + (371942616023979/10000000000000 : ℝ)*(f.sum) + (61083584770121/9321250000000000000000000000 : ℝ)*base66 + (32391804490036699209/3728500000000000000000000000000000 : ℝ)*base68 + (16815117685743699209/3728500000000000000000000000000000 : ℝ)*base70 + (43824532451206699209/3728500000000000000000000000000000 : ℝ)*base72 + (75543873817819/37285000000000000000000000000 : ℝ)*base74 + (20522896394125199209/3728500000000000000000000000000000 : ℝ)*base76 + (11287622520655699209/3728500000000000000000000000000000 : ℝ)*base78 + (28054218460060699209/3728500000000000000000000000000000 : ℝ)*base80 + (4998414882807/1165156250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (18056667/10000000000000000000000 : ℝ)*base90 + (18056667/10000000000000000000000 : ℝ)*base92 + (18056667/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9758857107375767901377470929/932125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (227816317/12500000000000 : ℝ)*(base19) + (14676873/1000000000000 : ℝ)*(base23) + (32365701/100000000000000 : ℝ)*(upper2) + (40955837/20000000000000 : ℝ)*(upper3) + (24699307/6250000000000 : ℝ)*(upper5) + (1308305162176347/50000000000000 : ℝ)*(major0) + (1308305162176347/50000000000000 : ℝ)*(major1) + (1308305162176347/50000000000000 : ℝ)*(major2) + (24642664877/100000000000000 : ℝ)*(sp1) + (4265121859/25000000000000 : ℝ)*(sp2) + (37783482502259/1000000000000 : ℝ)*(sp4) + (3778321785030487/100000000000000 : ℝ)*(sp5) + (944582430512791/25000000000000 : ℝ)*(sp6) + (727436024748533/50000000000000 : ℝ)*(sp7) + (727436024748533/50000000000000 : ℝ)*(f.failure) + (37783482502259/1000000000000 : ℝ)*(f.sum) + (104263439502889/18642500000000000000000000000 : ℝ)*base65 + (18035653278458201357/3728500000000000000000000000000000 : ℝ)*base68 + (14081186690992798643/3728500000000000000000000000000000 : ℝ)*base69 + (7092530774322201357/3728500000000000000000000000000000 : ℝ)*base72 + (14943333014873/37285000000000000000000000000 : ℝ)*base73 + (4050092365385201357/3728500000000000000000000000000000 : ℝ)*base76 + (3993467591143201357/3728500000000000000000000000000000 : ℝ)*base78 + (5934034520162201357/3728500000000000000000000000000000 : ℝ)*base80 + (46535289137339/18642500000000000000000000000 : ℝ)*base81 + (11513459/5000000000000000000000 : ℝ)*base90 + (11513459/5000000000000000000000 : ℝ)*base92 + (11513459/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1653_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3451/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4899/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (531/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1653_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1653_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (531/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1653_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1653_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1653_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (531/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1653_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
