-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1691_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:39:25.961182+00:00
-- url     : https://prove2.me/submissions/32e06b8d-1580-4770-8c81-9906f7100ecf

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
theorem support_rectangle_w1691_s3_0 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-370948539/2500000000 : ℝ)*x 0 + (1370632861/2500000000 : ℝ)*x 1 + (513546941/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (370948539/2500000000 : ℝ)^5151 ≤ (2310538118019/25000000000000 : ℝ)^4127 := by
    have hnat : (370948539 : ℕ)^5151*25000000000000^4127 ≤ 2310538118019^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370948539 2500000000 2310538118019 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1370632861/2500000000 : ℝ)^5151 ≤ (9445970198271/20000000000000 : ℝ)^4127 := by
    have hnat : (1370632861 : ℕ)^5151*20000000000000^4127 ≤ 9445970198271^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370632861 2500000000 9445970198271 20000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513546941/1000000000 : ℝ)^5151 ≤ (10881999133061/25000000000000 : ℝ)^4127 := by
    have hnat : (513546941 : ℕ)^5151*25000000000000^4127 ≤ 10881999133061^4127*1000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513546941 1000000000 10881999133061 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-370948539/2500000000 : ℝ), (1370632861/2500000000 : ℝ), (513546941/1000000000 : ℝ)] ![(2310538118019/25000000000000 : ℝ), (9445970198271/20000000000000 : ℝ), (10881999133061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-370948539/2500000000 : ℝ)|^5151 ≤ (2310538118019/25000000000000 : ℝ)^4127
        have hw : |(-370948539/2500000000 : ℝ)|=(370948539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1370632861/2500000000 : ℝ)|^5151 ≤ (9445970198271/20000000000000 : ℝ)^4127
        have hw : |(1370632861/2500000000 : ℝ)|=(1370632861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513546941/1000000000 : ℝ)|^5151 ≤ (10881999133061/25000000000000 : ℝ)^4127
        have hw : |(513546941/1000000000 : ℝ)|=(513546941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s3_1 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267494471/500000000 : ℝ)*x 0 + (-416012923/2500000000 : ℝ)*x 1 + (5135469453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267494471/500000000 : ℝ)^5151 ≤ (45807980091731/100000000000000 : ℝ)^4127 := by
    have hnat : (267494471 : ℕ)^5151*100000000000000^4127 ≤ 45807980091731^4127*500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267494471 500000000 45807980091731 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416012923/2500000000 : ℝ)^5151 ≤ (5332011456721/50000000000000 : ℝ)^4127 := by
    have hnat : (416012923 : ℕ)^5151*50000000000000^4127 ≤ 5332011456721^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416012923 2500000000 5332011456721 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135469453/10000000000 : ℝ)^5151 ≤ (21763998493571/50000000000000 : ℝ)^4127 := by
    have hnat : (5135469453 : ℕ)^5151*50000000000000^4127 ≤ 21763998493571^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135469453 10000000000 21763998493571 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267494471/500000000 : ℝ), (-416012923/2500000000 : ℝ), (5135469453/10000000000 : ℝ)] ![(45807980091731/100000000000000 : ℝ), (5332011456721/50000000000000 : ℝ), (21763998493571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267494471/500000000 : ℝ)|^5151 ≤ (45807980091731/100000000000000 : ℝ)^4127
        have hw : |(267494471/500000000 : ℝ)|=(267494471/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-416012923/2500000000 : ℝ)|^5151 ≤ (5332011456721/50000000000000 : ℝ)^4127
        have hw : |(-416012923/2500000000 : ℝ)|=(416012923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135469453/10000000000 : ℝ)|^5151 ≤ (21763998493571/50000000000000 : ℝ)^4127
        have hw : |(5135469453/10000000000 : ℝ)|=(5135469453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s3_2 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349886739/10000000000 : ℝ)*x 0 + (5135471951/10000000000 : ℝ)*x 1 + (-166405197/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349886739/10000000000 : ℝ)^5151 ≤ (11451987860011/25000000000000 : ℝ)^4127 := by
    have hnat : (5349886739 : ℕ)^5151*25000000000000^4127 ≤ 11451987860011^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349886739 10000000000 11451987860011 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5135471951/10000000000 : ℝ)^5151 ≤ (21764011706773/50000000000000 : ℝ)^4127 := by
    have hnat : (5135471951 : ℕ)^5151*50000000000000^4127 ≤ 21764011706773^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135471951 10000000000 21764011706773 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166405197/1000000000 : ℝ)^5151 ≤ (133300314213/1250000000000 : ℝ)^4127 := by
    have hnat : (166405197 : ℕ)^5151*1250000000000^4127 ≤ 133300314213^4127*1000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166405197 1000000000 133300314213 1250000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349886739/10000000000 : ℝ), (5135471951/10000000000 : ℝ), (-166405197/1000000000 : ℝ)] ![(11451987860011/25000000000000 : ℝ), (21764011706773/50000000000000 : ℝ), (133300314213/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349886739/10000000000 : ℝ)|^5151 ≤ (11451987860011/25000000000000 : ℝ)^4127
        have hw : |(5349886739/10000000000 : ℝ)|=(5349886739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5135471951/10000000000 : ℝ)|^5151 ≤ (21764011706773/50000000000000 : ℝ)^4127
        have hw : |(5135471951/10000000000 : ℝ)|=(5135471951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-166405197/1000000000 : ℝ)|^5151 ≤ (133300314213/1250000000000 : ℝ)^4127
        have hw : |(-166405197/1000000000 : ℝ)|=(166405197/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s3_3 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4129873263/10000000000 : ℝ)*x 0 + (3667190739/10000000000 : ℝ)*x 1 + (925978961/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4129873263/10000000000 : ℝ)^5151 ≤ (33162107981511/100000000000000 : ℝ)^4127 := by
    have hnat : (4129873263 : ℕ)^5151*100000000000000^4127 ≤ 33162107981511^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129873263 10000000000 33162107981511 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3667190739/10000000000 : ℝ)^5151 ≤ (893480387633/3125000000000 : ℝ)^4127 := by
    have hnat : (3667190739 : ℕ)^5151*3125000000000^4127 ≤ 893480387633^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3667190739 10000000000 893480387633 3125000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (925978961/2000000000 : ℝ)^5151 ≤ (47808149507/125000000000 : ℝ)^4127 := by
    have hnat : (925978961 : ℕ)^5151*125000000000^4127 ≤ 47808149507^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925978961 2000000000 47808149507 125000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4129873263/10000000000 : ℝ), (3667190739/10000000000 : ℝ), (925978961/2000000000 : ℝ)] ![(33162107981511/100000000000000 : ℝ), (893480387633/3125000000000 : ℝ), (47808149507/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4129873263/10000000000 : ℝ)|^5151 ≤ (33162107981511/100000000000000 : ℝ)^4127
        have hw : |(4129873263/10000000000 : ℝ)|=(4129873263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3667190739/10000000000 : ℝ)|^5151 ≤ (893480387633/3125000000000 : ℝ)^4127
        have hw : |(3667190739/10000000000 : ℝ)|=(3667190739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(925978961/2000000000 : ℝ)|^5151 ≤ (47808149507/125000000000 : ℝ)^4127
        have hw : |(925978961/2000000000 : ℝ)|=(925978961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s3_4 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-370988817/2500000000 : ℝ)*x 0 + (2569625961/5000000000 : ℝ)*x 1 + (1095738529/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (370988817/2500000000 : ℝ)^5151 ≤ (4621702504147/50000000000000 : ℝ)^4127 := by
    have hnat : (370988817 : ℕ)^5151*50000000000000^4127 ≤ 4621702504147^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370988817 2500000000 4621702504147 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569625961/5000000000 : ℝ)^5151 ≤ (4356801547421/10000000000000 : ℝ)^4127 := by
    have hnat : (2569625961 : ℕ)^5151*10000000000000^4127 ≤ 4356801547421^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569625961 5000000000 4356801547421 10000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095738529/2000000000 : ℝ)^5151 ≤ (11797144874951/25000000000000 : ℝ)^4127 := by
    have hnat : (1095738529 : ℕ)^5151*25000000000000^4127 ≤ 11797144874951^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095738529 2000000000 11797144874951 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-370988817/2500000000 : ℝ), (2569625961/5000000000 : ℝ), (1095738529/2000000000 : ℝ)] ![(4621702504147/50000000000000 : ℝ), (4356801547421/10000000000000 : ℝ), (11797144874951/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-370988817/2500000000 : ℝ)|^5151 ≤ (4621702504147/50000000000000 : ℝ)^4127
        have hw : |(-370988817/2500000000 : ℝ)|=(370988817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569625961/5000000000 : ℝ)|^5151 ≤ (4356801547421/10000000000000 : ℝ)^4127
        have hw : |(2569625961/5000000000 : ℝ)|=(2569625961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095738529/2000000000 : ℝ)|^5151 ≤ (11797144874951/25000000000000 : ℝ)^4127
        have hw : |(1095738529/2000000000 : ℝ)|=(1095738529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s3_5 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051418417/2000000000 : ℝ)*x 0 + (-1320832961/10000000000 : ℝ)*x 1 + (2739346239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051418417/2000000000 : ℝ)^5151 ≤ (11204600971223/25000000000000 : ℝ)^4127 := by
    have hnat : (1051418417 : ℕ)^5151*25000000000000^4127 ≤ 11204600971223^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051418417 2000000000 11204600971223 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320832961/10000000000 : ℝ)^5151 ≤ (7993018395183/100000000000000 : ℝ)^4127 := by
    have hnat : (1320832961 : ℕ)^5151*100000000000000^4127 ≤ 7993018395183^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320832961 10000000000 7993018395183 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2739346239/5000000000 : ℝ)^5151 ≤ (47188577704519/100000000000000 : ℝ)^4127 := by
    have hnat : (2739346239 : ℕ)^5151*100000000000000^4127 ≤ 47188577704519^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739346239 5000000000 47188577704519 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051418417/2000000000 : ℝ), (-1320832961/10000000000 : ℝ), (2739346239/5000000000 : ℝ)] ![(11204600971223/25000000000000 : ℝ), (7993018395183/100000000000000 : ℝ), (47188577704519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051418417/2000000000 : ℝ)|^5151 ≤ (11204600971223/25000000000000 : ℝ)^4127
        have hw : |(1051418417/2000000000 : ℝ)|=(1051418417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1320832961/10000000000 : ℝ)|^5151 ≤ (7993018395183/100000000000000 : ℝ)^4127
        have hw : |(-1320832961/10000000000 : ℝ)|=(1320832961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2739346239/5000000000 : ℝ)|^5151 ≤ (47188577704519/100000000000000 : ℝ)^4127
        have hw : |(2739346239/5000000000 : ℝ)|=(2739346239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s3_6 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314273063/2500000000 : ℝ)*x 0 + (5478692351/10000000000 : ℝ)*x 1 + (-660416453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314273063/2500000000 : ℝ)^5151 ≤ (44818405661879/100000000000000 : ℝ)^4127 := by
    have hnat : (1314273063 : ℕ)^5151*100000000000000^4127 ≤ 44818405661879^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314273063 2500000000 44818405661879 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5478692351/10000000000 : ℝ)^5151 ≤ (23594288169621/50000000000000 : ℝ)^4127 := by
    have hnat : (5478692351 : ℕ)^5151*50000000000000^4127 ≤ 23594288169621^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478692351 10000000000 23594288169621 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660416453/5000000000 : ℝ)^5151 ≤ (999127247471/12500000000000 : ℝ)^4127 := by
    have hnat : (660416453 : ℕ)^5151*12500000000000^4127 ≤ 999127247471^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660416453 5000000000 999127247471 12500000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314273063/2500000000 : ℝ), (5478692351/10000000000 : ℝ), (-660416453/5000000000 : ℝ)] ![(44818405661879/100000000000000 : ℝ), (23594288169621/50000000000000 : ℝ), (999127247471/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314273063/2500000000 : ℝ)|^5151 ≤ (44818405661879/100000000000000 : ℝ)^4127
        have hw : |(1314273063/2500000000 : ℝ)|=(1314273063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5478692351/10000000000 : ℝ)|^5151 ≤ (23594288169621/50000000000000 : ℝ)^4127
        have hw : |(5478692351/10000000000 : ℝ)|=(5478692351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-660416453/5000000000 : ℝ)|^5151 ≤ (999127247471/12500000000000 : ℝ)^4127
        have hw : |(-660416453/5000000000 : ℝ)|=(660416453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s3_7 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4130320531/10000000000 : ℝ)*x 0 + (4619408089/10000000000 : ℝ)*x 1 + (114932321/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4130320531/10000000000 : ℝ)^5151 ≤ (33166590645107/100000000000000 : ℝ)^4127 := by
    have hnat : (4130320531 : ℕ)^5151*100000000000000^4127 ≤ 33166590645107^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130320531 10000000000 33166590645107 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4619408089/10000000000 : ℝ)^5151 ≤ (19069213590017/50000000000000 : ℝ)^4127 := by
    have hnat : (4619408089 : ℕ)^5151*50000000000000^4127 ≤ 19069213590017^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4619408089 10000000000 19069213590017 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114932321/312500000 : ℝ)^5151 ≤ (5738996431057/20000000000000 : ℝ)^4127 := by
    have hnat : (114932321 : ℕ)^5151*20000000000000^4127 ≤ 5738996431057^4127*312500000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114932321 312500000 5738996431057 20000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4130320531/10000000000 : ℝ), (4619408089/10000000000 : ℝ), (114932321/312500000 : ℝ)] ![(33166590645107/100000000000000 : ℝ), (19069213590017/50000000000000 : ℝ), (5738996431057/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4130320531/10000000000 : ℝ)|^5151 ≤ (33166590645107/100000000000000 : ℝ)^4127
        have hw : |(4130320531/10000000000 : ℝ)|=(4130320531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4619408089/10000000000 : ℝ)|^5151 ≤ (19069213590017/50000000000000 : ℝ)^4127
        have hw : |(4619408089/10000000000 : ℝ)|=(4619408089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(114932321/312500000 : ℝ)|^5151 ≤ (5738996431057/20000000000000 : ℝ)^4127
        have hw : |(114932321/312500000 : ℝ)|=(114932321/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s3_8 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-23530577/2500000000 : ℝ)*x 0 + (1145032411/2000000000 : ℝ)*x 1 + (572503767/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23530577/2500000000 : ℝ)^5151 ≤ (147873676753/50000000000000 : ℝ)^4127 := by
    have hnat : (23530577 : ℕ)^5151*50000000000000^4127 ≤ 147873676753^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23530577 2500000000 147873676753 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1145032411/2000000000 : ℝ)^5151 ≤ (49852802236147/100000000000000 : ℝ)^4127 := by
    have hnat : (1145032411 : ℕ)^5151*100000000000000^4127 ≤ 49852802236147^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145032411 2000000000 49852802236147 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (572503767/1000000000 : ℝ)^5151 ≤ (49851450394843/100000000000000 : ℝ)^4127 := by
    have hnat : (572503767 : ℕ)^5151*100000000000000^4127 ≤ 49851450394843^4127*1000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572503767 1000000000 49851450394843 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23530577/2500000000 : ℝ), (1145032411/2000000000 : ℝ), (572503767/1000000000 : ℝ)] ![(147873676753/50000000000000 : ℝ), (49852802236147/100000000000000 : ℝ), (49851450394843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23530577/2500000000 : ℝ)|^5151 ≤ (147873676753/50000000000000 : ℝ)^4127
        have hw : |(-23530577/2500000000 : ℝ)|=(23530577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1145032411/2000000000 : ℝ)|^5151 ≤ (49852802236147/100000000000000 : ℝ)^4127
        have hw : |(1145032411/2000000000 : ℝ)|=(1145032411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(572503767/1000000000 : ℝ)|^5151 ≤ (49851450394843/100000000000000 : ℝ)^4127
        have hw : |(572503767/1000000000 : ℝ)|=(572503767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s3_9 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (461216601/5000000000 : ℝ)*x 0 + (-145850511/312500000 : ℝ)*x 1 + (6307699613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (461216601/5000000000 : ℝ)^5151 ≤ (5106371217263/100000000000000 : ℝ)^4127 := by
    have hnat : (461216601 : ℕ)^5151*100000000000000^4127 ≤ 5106371217263^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461216601 5000000000 5106371217263 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145850511/312500000 : ℝ)^5151 ≤ (38631705827037/100000000000000 : ℝ)^4127 := by
    have hnat : (145850511 : ℕ)^5151*100000000000000^4127 ≤ 38631705827037^4127*312500000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145850511 312500000 38631705827037 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6307699613/10000000000 : ℝ)^5151 ≤ (56261922938451/100000000000000 : ℝ)^4127 := by
    have hnat : (6307699613 : ℕ)^5151*100000000000000^4127 ≤ 56261922938451^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6307699613 10000000000 56261922938451 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(461216601/5000000000 : ℝ), (-145850511/312500000 : ℝ), (6307699613/10000000000 : ℝ)] ![(5106371217263/100000000000000 : ℝ), (38631705827037/100000000000000 : ℝ), (56261922938451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(461216601/5000000000 : ℝ)|^5151 ≤ (5106371217263/100000000000000 : ℝ)^4127
        have hw : |(461216601/5000000000 : ℝ)|=(461216601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-145850511/312500000 : ℝ)|^5151 ≤ (38631705827037/100000000000000 : ℝ)^4127
        have hw : |(-145850511/312500000 : ℝ)|=(145850511/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6307699613/10000000000 : ℝ)|^5151 ≤ (56261922938451/100000000000000 : ℝ)^4127
        have hw : |(6307699613/10000000000 : ℝ)|=(6307699613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s3_10 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1302766573/10000000000 : ℝ)*x 0 + (725088137/1000000000 : ℝ)*x 1 + (-1656822209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1302766573/10000000000 : ℝ)^5151 ≤ (157135903153/2000000000000 : ℝ)^4127 := by
    have hnat : (1302766573 : ℕ)^5151*2000000000000^4127 ≤ 157135903153^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302766573 10000000000 157135903153 2000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (725088137/1000000000 : ℝ)^5151 ≤ (6695001346643/10000000000000 : ℝ)^4127 := by
    have hnat : (725088137 : ℕ)^5151*10000000000000^4127 ≤ 6695001346643^4127*1000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      725088137 1000000000 6695001346643 10000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1656822209/5000000000 : ℝ)^5151 ≤ (25193191368751/100000000000000 : ℝ)^4127 := by
    have hnat : (1656822209 : ℕ)^5151*100000000000000^4127 ≤ 25193191368751^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656822209 5000000000 25193191368751 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1302766573/10000000000 : ℝ), (725088137/1000000000 : ℝ), (-1656822209/5000000000 : ℝ)] ![(157135903153/2000000000000 : ℝ), (6695001346643/10000000000000 : ℝ), (25193191368751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1302766573/10000000000 : ℝ)|^5151 ≤ (157135903153/2000000000000 : ℝ)^4127
        have hw : |(1302766573/10000000000 : ℝ)|=(1302766573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(725088137/1000000000 : ℝ)|^5151 ≤ (6695001346643/10000000000000 : ℝ)^4127
        have hw : |(725088137/1000000000 : ℝ)|=(725088137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1656822209/5000000000 : ℝ)|^5151 ≤ (25193191368751/100000000000000 : ℝ)^4127
        have hw : |(-1656822209/5000000000 : ℝ)|=(1656822209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s3_11 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350966941/10000000000 : ℝ)*x 0 + (2676060973/5000000000 : ℝ)*x 1 + (5362884411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350966941/10000000000 : ℝ)^5151 ≤ (8221261166447/100000000000000 : ℝ)^4127 := by
    have hnat : (1350966941 : ℕ)^5151*100000000000000^4127 ≤ 8221261166447^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350966941 10000000000 8221261166447 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2676060973/5000000000 : ℝ)^5151 ≤ (1145796005019/2500000000000 : ℝ)^4127 := by
    have hnat : (2676060973 : ℕ)^5151*2500000000000^4127 ≤ 1145796005019^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676060973 5000000000 1145796005019 2500000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5362884411/10000000000 : ℝ)^5151 ≤ (45946898620289/100000000000000 : ℝ)^4127 := by
    have hnat : (5362884411 : ℕ)^5151*100000000000000^4127 ≤ 45946898620289^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362884411 10000000000 45946898620289 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350966941/10000000000 : ℝ), (2676060973/5000000000 : ℝ), (5362884411/10000000000 : ℝ)] ![(8221261166447/100000000000000 : ℝ), (1145796005019/2500000000000 : ℝ), (45946898620289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350966941/10000000000 : ℝ)|^5151 ≤ (8221261166447/100000000000000 : ℝ)^4127
        have hw : |(1350966941/10000000000 : ℝ)|=(1350966941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2676060973/5000000000 : ℝ)|^5151 ≤ (1145796005019/2500000000000 : ℝ)^4127
        have hw : |(2676060973/5000000000 : ℝ)|=(2676060973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5362884411/10000000000 : ℝ)|^5151 ≤ (45946898620289/100000000000000 : ℝ)^4127
        have hw : |(5362884411/10000000000 : ℝ)|=(5362884411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1691_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (69/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4911/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9841/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4307/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (69/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4911/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (69/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4911/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (69/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4911/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (69/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4911/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (69/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4911/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (69/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4911/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4911/50000 : ℝ) ^ (5143/1024 : ℝ) ≤ (433843923404869/50000000000000000000 : ℝ) := by
    have hpowers : (4911/50000 : ℝ)^5143 ≤ (433843923404869/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4911 : ℕ)^5143*50000000000000000000^1024 ≤ 433843923404869^1024*50000^5143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4911 50000 433843923404869 50000000000000000000 5143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4911/50000 : ℝ)) (X := (433843923404869/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (69/400 : ℝ) ^ (5143/1024 : ℝ) ≤ (14682603289462137/100000000000000000000 : ℝ) := by
    have hpowers : (69/400 : ℝ)^5143 ≤ (14682603289462137/100000000000000000000 : ℝ)^1024 := by
      have hnat : (69 : ℕ)^5143*100000000000000000000^1024 ≤ 14682603289462137^1024*400^5143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69 400 14682603289462137 100000000000000000000 5143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69/400 : ℝ)) (X := (14682603289462137/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000433843923404869/25000000000000000000 : ℝ) ≤ (10000034552058359/10000000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (25000433843923404869/25000000000000000000 : ℝ)^1024 ≤ (10000034552058359/10000000000000000 : ℝ)^5143 := by
      have hnat : (25000433843923404869 : ℕ)^1024*10000000000000000^5143 ≤ 10000034552058359^5143*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000433843923404869 25000000000000000000 10000034552058359 10000000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000034552058359/10000000000000000 : ℝ)) (X := (25000433843923404869/25000000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (32004976093163607/32000000000000000 : ℝ) ≤ (2000061919139213/2000000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (32004976093163607/32000000000000000 : ℝ)^1024 ≤ (2000061919139213/2000000000000000 : ℝ)^5143 := by
      have hnat : (32004976093163607 : ℕ)^1024*2000000000000000^5143 ≤ 2000061919139213^5143*32000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32004976093163607 32000000000000000 2000061919139213 2000000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000061919139213/2000000000000000 : ℝ)) (X := (32004976093163607/32000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014682603289462137/50000000000000000000 : ℝ) ≤ (10000584639333771/10000000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (50014682603289462137/50000000000000000000 : ℝ)^1024 ≤ (10000584639333771/10000000000000000 : ℝ)^5143 := by
      have hnat : (50014682603289462137 : ℕ)^1024*10000000000000000^5143 ≤ 10000584639333771^5143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014682603289462137 50000000000000000000 10000584639333771 10000000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000584639333771/10000000000000000 : ℝ)) (X := (50014682603289462137/50000000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(433843923404869/50000000000000000000 : ℝ) ≤ ((6189571141289199499/6190000000000000000 : ℝ)+2*(137521818853/371400000000000 : ℝ)*(4911/50000 : ℝ))^(5143/1024 : ℝ) := by
    rw [show (6189571141289199499/6190000000000000000 : ℝ)+2*(137521818853/371400000000000 : ℝ)*(4911/50000 : ℝ)=(10000034552058359/10000000000000000 : ℝ) by norm_num, show 1+2*(433843923404869/50000000000000000000 : ℝ)=(25000433843923404869/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14682603289462137/100000000000000000000 : ℝ)+(433843923404869/50000000000000000000 : ℝ) ≤ ((6189571141289199499/6190000000000000000 : ℝ)+(137521818853/371400000000000 : ℝ)*((69/400 : ℝ)+(4911/50000 : ℝ)))^(5143/1024 : ℝ) := by
    rw [show (6189571141289199499/6190000000000000000 : ℝ)+(137521818853/371400000000000 : ℝ)*((69/400 : ℝ)+(4911/50000 : ℝ))=(2000061919139213/2000000000000000 : ℝ) by norm_num, show 1+(14682603289462137/100000000000000000000 : ℝ)+(433843923404869/50000000000000000000 : ℝ)=(32004976093163607/32000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14682603289462137/100000000000000000000 : ℝ) ≤ ((6189571141289199499/6190000000000000000 : ℝ)+2*(137521818853/371400000000000 : ℝ)*(69/400 : ℝ))^(5143/1024 : ℝ) := by
    rw [show (6189571141289199499/6190000000000000000 : ℝ)+2*(137521818853/371400000000000 : ℝ)*(69/400 : ℝ)=(10000584639333771/10000000000000000 : ℝ) by norm_num, show 1+2*(14682603289462137/100000000000000000000 : ℝ)=(50014682603289462137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6189571141289199499/6190000000000000000 : ℝ)*(X 1 0+X 2 0)+(137521818853/371400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (4911/50000 : ℝ)) (hi := (69/400 : ℝ)) (c := (6189571141289199499/6190000000000000000 : ℝ)) (alpha := (137521818853/371400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6189571141289199499/6190000000000000000 : ℝ)*(X 0 1+X 2 1)+(137521818853/371400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (4911/50000 : ℝ)) (hi := (69/400 : ℝ)) (c := (6189571141289199499/6190000000000000000 : ℝ)) (alpha := (137521818853/371400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6189571141289199499/6190000000000000000 : ℝ)*(X 0 2+X 1 2)+(137521818853/371400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (4911/50000 : ℝ)) (hi := (69/400 : ℝ)) (c := (6189571141289199499/6190000000000000000 : ℝ)) (alpha := (137521818853/371400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-370948539/2500000000 : ℝ)*X 0 0+(1370632861/2500000000 : ℝ)*X 0 1+(513546941/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267494471/500000000 : ℝ)*X 1 0+(-416012923/2500000000 : ℝ)*X 1 1+(5135469453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349886739/10000000000 : ℝ)*X 2 0+(5135471951/10000000000 : ℝ)*X 2 1+(-166405197/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4129873263/10000000000 : ℝ)*X 0 0+(3667190739/10000000000 : ℝ)*X 0 1+(925978961/2000000000 : ℝ)*X 0 2+(4129873263/10000000000 : ℝ)*X 1 0+(3667190739/10000000000 : ℝ)*X 1 1+(925978961/2000000000 : ℝ)*X 1 2+(4129873263/10000000000 : ℝ)*X 2 0+(3667190739/10000000000 : ℝ)*X 2 1+(925978961/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-370988817/2500000000 : ℝ)*X 0 0+(2569625961/5000000000 : ℝ)*X 0 1+(1095738529/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1051418417/2000000000 : ℝ)*X 1 0+(-1320832961/10000000000 : ℝ)*X 1 1+(2739346239/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314273063/2500000000 : ℝ)*X 2 0+(5478692351/10000000000 : ℝ)*X 2 1+(-660416453/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4130320531/10000000000 : ℝ)*X 0 0+(4619408089/10000000000 : ℝ)*X 0 1+(114932321/312500000 : ℝ)*X 0 2+(4130320531/10000000000 : ℝ)*X 1 0+(4619408089/10000000000 : ℝ)*X 1 1+(114932321/312500000 : ℝ)*X 1 2+(4130320531/10000000000 : ℝ)*X 2 0+(4619408089/10000000000 : ℝ)*X 2 1+(114932321/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-23530577/2500000000 : ℝ)*X 0 0+(1145032411/2000000000 : ℝ)*X 0 1+(572503767/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((461216601/5000000000 : ℝ)*X 1 0+(-145850511/312500000 : ℝ)*X 1 1+(6307699613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1302766573/10000000000 : ℝ)*X 2 0+(725088137/1000000000 : ℝ)*X 2 1+(-1656822209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1350966941/10000000000 : ℝ)*X 0 0+(2676060973/5000000000 : ℝ)*X 0 1+(5362884411/10000000000 : ℝ)*X 0 2+(1350966941/10000000000 : ℝ)*X 1 0+(2676060973/5000000000 : ℝ)*X 1 1+(5362884411/10000000000 : ℝ)*X 1 2+(1350966941/10000000000 : ℝ)*X 2 0+(2676060973/5000000000 : ℝ)*X 2 1+(5362884411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2440391956221092290253529/38687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (269738671/100000000000000 : ℝ)*(lower3) + (95134409/20000000000000 : ℝ)*(lower4) + (245007630486281/12500000000000 : ℝ)*(major0) + (245007630486281/12500000000000 : ℝ)*(major1) + (245007630486281/12500000000000 : ℝ)*(major2) + (1440676980376439/50000000000000 : ℝ)*(sp0) + (1440682169288627/50000000000000 : ℝ)*(sp1) + (1440687700398299/50000000000000 : ℝ)*(sp2) + (41549810187199/4000000000000 : ℝ)*(sp3) + (9989303571/50000000000000 : ℝ)*(sp4) + (10739760461/100000000000000 : ℝ)*(sp5) + (2891637833/100000000000000 : ℝ)*(sp8) + (1752660139/100000000000000 : ℝ)*(sp9) + (715100627/50000000000000 : ℝ)*(sp10) + (41549810187199/4000000000000 : ℝ)*(f.failure) + (720344207749463/25000000000000 : ℝ)*(f.sum) + (22742434011227/9285000000000000000000000000 : ℝ)*base65 + (2157918182650369657/232125000000000000000000000000000 : ℝ)*base67 + (3588822462354994657/232125000000000000000000000000000 : ℝ)*base69 + (1897486404262369657/232125000000000000000000000000000 : ℝ)*base71 + (1640679563873/2321250000000000000000000000 : ℝ)*base73 + (1868669679282619657/232125000000000000000000000000000 : ℝ)*base75 + (2206547489700244657/232125000000000000000000000000000 : ℝ)*base77 + (3825617666937994657/232125000000000000000000000000000 : ℝ)*base79 + (26798987317517/9285000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/50000000000000 : ℝ)*base85 + (2169933/200000000000000000000 : ℝ)*base90 + (2169933/200000000000000000000 : ℝ)*base92 + (2169933/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1657114829942418532311573319/309500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (512321/390625000000 : ℝ)*(lower4) + (2004038709307091/100000000000000 : ℝ)*(major0) + (2004038709307091/100000000000000 : ℝ)*(major1) + (2004038709307091/100000000000000 : ℝ)*(major2) + (55443721/2500000000000 : ℝ)*(sp0) + (88144543/20000000000000 : ℝ)*(sp1) + (2946022878314033/100000000000000 : ℝ)*(sp4) + (589205055239137/20000000000000 : ℝ)*(sp5) + (736506316347791/25000000000000 : ℝ)*(sp6) + (1062051090192639/100000000000000 : ℝ)*(sp7) + (42559317/6250000000000 : ℝ)*(sp8) + (12018709/20000000000000 : ℝ)*(sp9) + (511620781/100000000000000 : ℝ)*(sp10) + (186468673/50000000000000 : ℝ)*(sp11) + (212410292625997/20000000000000 : ℝ)*(f.failure) + (589205155402389/20000000000000 : ℝ)*(f.sum) + (59419385839327/18570000000000000000000000000 : ℝ)*base66 + (2336216197613192227/1857000000000000000000000000000000 : ℝ)*base67 + (10408800570671192227/1857000000000000000000000000000000 : ℝ)*base69 + (8051880254324192227/1857000000000000000000000000000000 : ℝ)*base71 + (21067701640117/18570000000000000000000000000 : ℝ)*base74 + (2052919908026192227/1857000000000000000000000000000000 : ℝ)*base75 + (12208022249642192227/1857000000000000000000000000000000 : ℝ)*base77 + (2565876609497192227/1857000000000000000000000000000000 : ℝ)*base79 + (12267366826583/18570000000000000000000000000 : ℝ)*base81 + (1384599/1000000000000000000000 : ℝ)*base90 + (1384599/1000000000000000000000 : ℝ)*base92 + (1384599/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1691_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (69/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4911/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9841/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4307/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1691_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1691_s4_0 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674936597/5000000000 : ℝ)*x 0 + (5135512023/10000000000 : ℝ)*x 1 + (-416004267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674936597/5000000000 : ℝ)^5151 ≤ (4580780668549/10000000000000 : ℝ)^4127 := by
    have hnat : (2674936597 : ℕ)^5151*10000000000000^4127 ≤ 4580780668549^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674936597 5000000000 4580780668549 10000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5135512023/10000000000 : ℝ)^5151 ≤ (10882111834167/25000000000000 : ℝ)^4127 := by
    have hnat : (5135512023 : ℕ)^5151*25000000000000^4127 ≤ 10882111834167^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135512023 10000000000 10882111834167 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416004267/2500000000 : ℝ)^5151 ≤ (2132749194463/20000000000000 : ℝ)^4127 := by
    have hnat : (416004267 : ℕ)^5151*20000000000000^4127 ≤ 2132749194463^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416004267 2500000000 2132749194463 20000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674936597/5000000000 : ℝ), (5135512023/10000000000 : ℝ), (-416004267/2500000000 : ℝ)] ![(4580780668549/10000000000000 : ℝ), (10882111834167/25000000000000 : ℝ), (2132749194463/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674936597/5000000000 : ℝ)|^5151 ≤ (4580780668549/10000000000000 : ℝ)^4127
        have hw : |(2674936597/5000000000 : ℝ)|=(2674936597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5135512023/10000000000 : ℝ)|^5151 ≤ (10882111834167/25000000000000 : ℝ)^4127
        have hw : |(5135512023/10000000000 : ℝ)|=(5135512023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416004267/2500000000 : ℝ)|^5151 ≤ (2132749194463/20000000000000 : ℝ)^4127
        have hw : |(-416004267/2500000000 : ℝ)|=(416004267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s4_1 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-11593501/78125000 : ℝ)*x 0 + (1284822557/2500000000 : ℝ)*x 1 + (2739322821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11593501/78125000 : ℝ)^5151 ≤ (4621752493751/50000000000000 : ℝ)^4127 := by
    have hnat : (11593501 : ℕ)^5151*50000000000000^4127 ≤ 4621752493751^4127*78125000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11593501 78125000 4621752493751 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284822557/2500000000 : ℝ)^5151 ≤ (21784210394363/50000000000000 : ℝ)^4127 := by
    have hnat : (1284822557 : ℕ)^5151*50000000000000^4127 ≤ 21784210394363^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284822557 2500000000 21784210394363 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2739322821/5000000000 : ℝ)^5151 ≤ (9437614841621/20000000000000 : ℝ)^4127 := by
    have hnat : (2739322821 : ℕ)^5151*20000000000000^4127 ≤ 9437614841621^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739322821 5000000000 9437614841621 20000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11593501/78125000 : ℝ), (1284822557/2500000000 : ℝ), (2739322821/5000000000 : ℝ)] ![(4621752493751/50000000000000 : ℝ), (21784210394363/50000000000000 : ℝ), (9437614841621/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11593501/78125000 : ℝ)|^5151 ≤ (4621752493751/50000000000000 : ℝ)^4127
        have hw : |(-11593501/78125000 : ℝ)|=(11593501/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284822557/2500000000 : ℝ)|^5151 ≤ (21784210394363/50000000000000 : ℝ)^4127
        have hw : |(1284822557/2500000000 : ℝ)|=(1284822557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2739322821/5000000000 : ℝ)|^5151 ≤ (9437614841621/20000000000000 : ℝ)^4127
        have hw : |(2739322821/5000000000 : ℝ)|=(2739322821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s4_2 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051420541/2000000000 : ℝ)*x 0 + (-660442323/5000000000 : ℝ)*x 1 + (5478645653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051420541/2000000000 : ℝ)^5151 ≤ (5602314611069/12500000000000 : ℝ)^4127 := by
    have hnat : (1051420541 : ℕ)^5151*12500000000000^4127 ≤ 5602314611069^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051420541 2000000000 5602314611069 12500000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660442323/5000000000 : ℝ)^5151 ≤ (7993408774343/100000000000000 : ℝ)^4127 := by
    have hnat : (660442323 : ℕ)^5151*100000000000000^4127 ≤ 7993408774343^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660442323 5000000000 7993408774343 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5478645653/10000000000 : ℝ)^5151 ≤ (47188074326357/100000000000000 : ℝ)^4127 := by
    have hnat : (5478645653 : ℕ)^5151*100000000000000^4127 ≤ 47188074326357^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478645653 10000000000 47188074326357 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051420541/2000000000 : ℝ), (-660442323/5000000000 : ℝ), (5478645653/10000000000 : ℝ)] ![(5602314611069/12500000000000 : ℝ), (7993408774343/100000000000000 : ℝ), (47188074326357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051420541/2000000000 : ℝ)|^5151 ≤ (5602314611069/12500000000000 : ℝ)^4127
        have hw : |(1051420541/2000000000 : ℝ)|=(1051420541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-660442323/5000000000 : ℝ)|^5151 ≤ (7993408774343/100000000000000 : ℝ)^4127
        have hw : |(-660442323/5000000000 : ℝ)|=(660442323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5478645653/10000000000 : ℝ)|^5151 ≤ (47188074326357/100000000000000 : ℝ)^4127
        have hw : |(5478645653/10000000000 : ℝ)|=(5478645653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s4_3 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52571027/100000000 : ℝ)*x 0 + (2739322833/5000000000 : ℝ)*x 1 + (-660442317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52571027/100000000 : ℝ)^5151 ≤ (11204629208837/25000000000000 : ℝ)^4127 := by
    have hnat : (52571027 : ℕ)^5151*25000000000000^4127 ≤ 11204629208837^4127*100000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52571027 100000000 11204629208837 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2739322833/5000000000 : ℝ)^5151 ≤ (4718807446611/10000000000000 : ℝ)^4127 := by
    have hnat : (2739322833 : ℕ)^5151*10000000000000^4127 ≤ 4718807446611^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739322833 5000000000 4718807446611 10000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660442317/5000000000 : ℝ)^5151 ≤ (3996704341853/50000000000000 : ℝ)^4127 := by
    have hnat : (660442317 : ℕ)^5151*50000000000000^4127 ≤ 3996704341853^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660442317 5000000000 3996704341853 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52571027/100000000 : ℝ), (2739322833/5000000000 : ℝ), (-660442317/5000000000 : ℝ)] ![(11204629208837/25000000000000 : ℝ), (4718807446611/10000000000000 : ℝ), (3996704341853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52571027/100000000 : ℝ)|^5151 ≤ (11204629208837/25000000000000 : ℝ)^4127
        have hw : |(52571027/100000000 : ℝ)|=(52571027/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2739322833/5000000000 : ℝ)|^5151 ≤ (4718807446611/10000000000000 : ℝ)^4127
        have hw : |(2739322833/5000000000 : ℝ)|=(2739322833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-660442317/5000000000 : ℝ)|^5151 ≤ (3996704341853/50000000000000 : ℝ)^4127
        have hw : |(-660442317/5000000000 : ℝ)|=(660442317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s4_4 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2065164327/5000000000 : ℝ)*x 0 + (2309644863/5000000000 : ℝ)*x 1 + (3677951161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2065164327/5000000000 : ℝ)^5151 ≤ (33166672057537/100000000000000 : ℝ)^4127 := by
    have hnat : (2065164327 : ℕ)^5151*100000000000000^4127 ≤ 33166672057537^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065164327 5000000000 33166672057537 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2309644863/5000000000 : ℝ)^5151 ≤ (19068603746913/50000000000000 : ℝ)^4127 := by
    have hnat : (2309644863 : ℕ)^5151*50000000000000^4127 ≤ 19068603746913^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309644863 5000000000 19068603746913 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3677951161/10000000000 : ℝ)^5151 ≤ (1147844817111/4000000000000 : ℝ)^4127 := by
    have hnat : (3677951161 : ℕ)^5151*4000000000000^4127 ≤ 1147844817111^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3677951161 10000000000 1147844817111 4000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2065164327/5000000000 : ℝ), (2309644863/5000000000 : ℝ), (3677951161/10000000000 : ℝ)] ![(33166672057537/100000000000000 : ℝ), (19068603746913/50000000000000 : ℝ), (1147844817111/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2065164327/5000000000 : ℝ)|^5151 ≤ (33166672057537/100000000000000 : ℝ)^4127
        have hw : |(2065164327/5000000000 : ℝ)|=(2065164327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2309644863/5000000000 : ℝ)|^5151 ≤ (19068603746913/50000000000000 : ℝ)^4127
        have hw : |(2309644863/5000000000 : ℝ)|=(2309644863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3677951161/10000000000 : ℝ)|^5151 ≤ (1147844817111/4000000000000 : ℝ)^4127
        have hw : |(3677951161/10000000000 : ℝ)|=(3677951161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1691_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4307/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9841/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9841/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17227/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4307/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9841/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4307/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9841/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4307/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9841/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4307/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9841/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4307/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9841/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4307/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9841/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9841/100000 : ℝ) ^ (5143/1024 : ℝ) ≤ (54759426804569/6250000000000000000 : ℝ) := by
    have hpowers : (9841/100000 : ℝ)^5143 ≤ (54759426804569/6250000000000000000 : ℝ)^1024 := by
      have hnat : (9841 : ℕ)^5143*6250000000000000000^1024 ≤ 54759426804569^1024*100000^5143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9841 100000 54759426804569 6250000000000000000 5143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9841/100000 : ℝ)) (X := (54759426804569/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4307/25000 : ℝ) ^ (5143/1024 : ℝ) ≤ (14588795429014029/100000000000000000000 : ℝ) := by
    have hpowers : (4307/25000 : ℝ)^5143 ≤ (14588795429014029/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4307 : ℕ)^5143*100000000000000000000^1024 ≤ 14588795429014029^1024*25000^5143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4307 25000 14588795429014029 100000000000000000000 5143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4307/25000 : ℝ)) (X := (14588795429014029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125054759426804569/3125000000000000000 : ℝ) ≤ (2500008722264761/2500000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (3125054759426804569/3125000000000000000 : ℝ)^1024 ≤ (2500008722264761/2500000000000000 : ℝ)^5143 := by
      have hnat : (3125054759426804569 : ℕ)^1024*2500000000000000^5143 ≤ 2500008722264761^5143*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125054759426804569 3125000000000000000 2500008722264761 2500000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500008722264761/2500000000000000 : ℝ)) (X := (3125054759426804569/3125000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100015464946257887133/100000000000000000000 : ℝ) ≤ (10000307896642929/10000000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (100015464946257887133/100000000000000000000 : ℝ)^1024 ≤ (10000307896642929/10000000000000000 : ℝ)^5143 := by
      have hnat : (100015464946257887133 : ℕ)^1024*10000000000000000^5143 ≤ 10000307896642929^5143*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015464946257887133 100000000000000000000 10000307896642929 10000000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000307896642929/10000000000000000 : ℝ)) (X := (100015464946257887133/100000000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014588795429014029/50000000000000000000 : ℝ) ≤ (5000290452113407/5000000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (50014588795429014029/50000000000000000000 : ℝ)^1024 ≤ (5000290452113407/5000000000000000 : ℝ)^5143 := by
      have hnat : (50014588795429014029 : ℕ)^1024*5000000000000000^5143 ≤ 5000290452113407^5143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014588795429014029 50000000000000000000 5000290452113407 5000000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000290452113407/5000000000000000 : ℝ)) (X := (50014588795429014029/50000000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(54759426804569/6250000000000000000 : ℝ) ≤ ((36932442195106566729/36935000000000000000 : ℝ)+2*(54601516777/147740000000000 : ℝ)*(9841/100000 : ℝ))^(5143/1024 : ℝ) := by
    rw [show (36932442195106566729/36935000000000000000 : ℝ)+2*(54601516777/147740000000000 : ℝ)*(9841/100000 : ℝ)=(2500008722264761/2500000000000000 : ℝ) by norm_num, show 1+2*(54759426804569/6250000000000000000 : ℝ)=(3125054759426804569/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14588795429014029/100000000000000000000 : ℝ)+(54759426804569/6250000000000000000 : ℝ) ≤ ((36932442195106566729/36935000000000000000 : ℝ)+(54601516777/147740000000000 : ℝ)*((4307/25000 : ℝ)+(9841/100000 : ℝ)))^(5143/1024 : ℝ) := by
    rw [show (36932442195106566729/36935000000000000000 : ℝ)+(54601516777/147740000000000 : ℝ)*((4307/25000 : ℝ)+(9841/100000 : ℝ))=(10000307896642929/10000000000000000 : ℝ) by norm_num, show 1+(14588795429014029/100000000000000000000 : ℝ)+(54759426804569/6250000000000000000 : ℝ)=(100015464946257887133/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14588795429014029/100000000000000000000 : ℝ) ≤ ((36932442195106566729/36935000000000000000 : ℝ)+2*(54601516777/147740000000000 : ℝ)*(4307/25000 : ℝ))^(5143/1024 : ℝ) := by
    rw [show (36932442195106566729/36935000000000000000 : ℝ)+2*(54601516777/147740000000000 : ℝ)*(4307/25000 : ℝ)=(5000290452113407/5000000000000000 : ℝ) by norm_num, show 1+2*(14588795429014029/100000000000000000000 : ℝ)=(50014588795429014029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36932442195106566729/36935000000000000000 : ℝ)*(X 1 0+X 2 0)+(54601516777/147740000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (9841/100000 : ℝ)) (hi := (4307/25000 : ℝ)) (c := (36932442195106566729/36935000000000000000 : ℝ)) (alpha := (54601516777/147740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36932442195106566729/36935000000000000000 : ℝ)*(X 0 1+X 2 1)+(54601516777/147740000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (9841/100000 : ℝ)) (hi := (4307/25000 : ℝ)) (c := (36932442195106566729/36935000000000000000 : ℝ)) (alpha := (54601516777/147740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36932442195106566729/36935000000000000000 : ℝ)*(X 0 2+X 1 2)+(54601516777/147740000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (9841/100000 : ℝ)) (hi := (4307/25000 : ℝ)) (c := (36932442195106566729/36935000000000000000 : ℝ)) (alpha := (54601516777/147740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2674936597/5000000000 : ℝ)*X 2 0+(5135512023/10000000000 : ℝ)*X 2 1+(-416004267/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s4_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-11593501/78125000 : ℝ)*X 0 0+(1284822557/2500000000 : ℝ)*X 0 1+(2739322821/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s4_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1051420541/2000000000 : ℝ)*X 1 0+(-660442323/5000000000 : ℝ)*X 1 1+(5478645653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s4_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((52571027/100000000 : ℝ)*X 2 0+(2739322833/5000000000 : ℝ)*X 2 1+(-660442317/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s4_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2065164327/5000000000 : ℝ)*X 0 0+(2309644863/5000000000 : ℝ)*X 0 1+(3677951161/10000000000 : ℝ)*X 0 2+(2065164327/5000000000 : ℝ)*X 1 0+(2309644863/5000000000 : ℝ)*X 1 1+(3677951161/10000000000 : ℝ)*X 1 2+(2065164327/5000000000 : ℝ)*X 2 0+(2309644863/5000000000 : ℝ)*X 2 1+(3677951161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s4_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4022589884537289121557614757/923375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79230103/12500000000000 : ℝ)*(base19) + (84913991/12500000000000 : ℝ)*(base23) + (188633983/100000000000000 : ℝ)*(lower1) + (20237869/20000000000000 : ℝ)*(upper3) + (19400663/100000000000000 : ℝ)*(lower4) + (86457119/100000000000000 : ℝ)*(upper5) + (1002268052962111/50000000000000 : ℝ)*(major0) + (1002268052962111/50000000000000 : ℝ)*(major1) + (1002268052962111/50000000000000 : ℝ)*(major2) + (161078693/25000000000000 : ℝ)*(sp0) + (1473378502700359/50000000000000 : ℝ)*(sp1) + (1473378185779947/50000000000000 : ℝ)*(sp2) + (46043057527719/1562500000000 : ℝ)*(sp3) + (66394691327151/6250000000000 : ℝ)*(sp4) + (66394691327151/6250000000000 : ℝ)*(f.failure) + (1473378502700359/50000000000000 : ℝ)*(f.sum) + (9974186394713/3693500000000000000000000000 : ℝ)*base66 + (11614209927418045081/1846750000000000000000000000000000 : ℝ)*base68 + (11647145258429045081/1846750000000000000000000000000000 : ℝ)*base70 + (32151871642572545081/1846750000000000000000000000000000 : ℝ)*base72 + (2007382127591/738700000000000000000000000 : ℝ)*base74 + (33730341359594545081/1846750000000000000000000000000000 : ℝ)*base76 + (16403707259145954919/1846750000000000000000000000000000 : ℝ)*base77 + (19945390750582954919/1846750000000000000000000000000000 : ℝ)*base79 + (22596789777769/3693500000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base88 + (981517/312500000000000000000 : ℝ)*base90 + (981517/312500000000000000000 : ℝ)*base92 + (981517/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1691_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4307/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9841/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9841/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17227/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1691_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1691_box_0 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-45988529/400000000 : ℝ)*x 0 + (339219279/625000000 : ℝ)*x 1 + (2713754487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45988529/400000000 : ℝ)^5151 ≤ (6722038669263/100000000000000 : ℝ)^4127 := by
    have hnat : (45988529 : ℕ)^5151*100000000000000^4127 ≤ 6722038669263^4127*400000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45988529 400000000 6722038669263 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339219279/625000000 : ℝ)^5151 ≤ (46638977923271/100000000000000 : ℝ)^4127 := by
    have hnat : (339219279 : ℕ)^5151*100000000000000^4127 ≤ 46638977923271^4127*625000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339219279 625000000 46638977923271 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713754487/5000000000 : ℝ)^5151 ≤ (23319491696563/50000000000000 : ℝ)^4127 := by
    have hnat : (2713754487 : ℕ)^5151*50000000000000^4127 ≤ 23319491696563^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713754487 5000000000 23319491696563 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45988529/400000000 : ℝ), (339219279/625000000 : ℝ), (2713754487/5000000000 : ℝ)] ![(6722038669263/100000000000000 : ℝ), (46638977923271/100000000000000 : ℝ), (23319491696563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45988529/400000000 : ℝ)|^5151 ≤ (6722038669263/100000000000000 : ℝ)^4127
        have hw : |(-45988529/400000000 : ℝ)|=(45988529/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339219279/625000000 : ℝ)|^5151 ≤ (46638977923271/100000000000000 : ℝ)^4127
        have hw : |(339219279/625000000 : ℝ)|=(339219279/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713754487/5000000000 : ℝ)|^5151 ≤ (23319491696563/50000000000000 : ℝ)^4127
        have hw : |(2713754487/5000000000 : ℝ)|=(2713754487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_1 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226026771/10000000000 : ℝ)*x 0 + (-143610891/1000000000 : ℝ)*x 1 + (135687719/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226026771/10000000000 : ℝ)^5151 ≤ (44488091652287/100000000000000 : ℝ)^4127 := by
    have hnat : (5226026771 : ℕ)^5151*100000000000000^4127 ≤ 44488091652287^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226026771 10000000000 44488091652287 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (143610891/1000000000 : ℝ)^5151 ≤ (8872927227957/100000000000000 : ℝ)^4127 := by
    have hnat : (143610891 : ℕ)^5151*100000000000000^4127 ≤ 8872927227957^4127*1000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143610891 1000000000 8872927227957 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135687719/250000000 : ℝ)^5151 ≤ (11659745274483/25000000000000 : ℝ)^4127 := by
    have hnat : (135687719 : ℕ)^5151*25000000000000^4127 ≤ 11659745274483^4127*250000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135687719 250000000 11659745274483 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226026771/10000000000 : ℝ), (-143610891/1000000000 : ℝ), (135687719/250000000 : ℝ)] ![(44488091652287/100000000000000 : ℝ), (8872927227957/100000000000000 : ℝ), (11659745274483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226026771/10000000000 : ℝ)|^5151 ≤ (44488091652287/100000000000000 : ℝ)^4127
        have hw : |(5226026771/10000000000 : ℝ)|=(5226026771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-143610891/1000000000 : ℝ)|^5151 ≤ (8872927227957/100000000000000 : ℝ)^4127
        have hw : |(-143610891/1000000000 : ℝ)|=(143610891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135687719/250000000 : ℝ)|^5151 ≤ (11659745274483/25000000000000 : ℝ)^4127
        have hw : |(135687719/250000000 : ℝ)|=(135687719/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_2 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52260269/100000000 : ℝ)*x 0 + (1085501741/2000000000 : ℝ)*x 1 + (-143610881/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52260269/100000000 : ℝ)^5151 ≤ (44488093022913/100000000000000 : ℝ)^4127 := by
    have hnat : (52260269 : ℕ)^5151*100000000000000^4127 ≤ 44488093022913^4127*100000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52260269 100000000 44488093022913 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085501741/2000000000 : ℝ)^5151 ≤ (23319490254023/50000000000000 : ℝ)^4127 := by
    have hnat : (1085501741 : ℕ)^5151*50000000000000^4127 ≤ 23319490254023^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085501741 2000000000 23319490254023 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (143610881/1000000000 : ℝ)^5151 ≤ (8872926456811/100000000000000 : ℝ)^4127 := by
    have hnat : (143610881 : ℕ)^5151*100000000000000^4127 ≤ 8872926456811^4127*1000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143610881 1000000000 8872926456811 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52260269/100000000 : ℝ), (1085501741/2000000000 : ℝ), (-143610881/1000000000 : ℝ)] ![(44488093022913/100000000000000 : ℝ), (23319490254023/50000000000000 : ℝ), (8872926456811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52260269/100000000 : ℝ)|^5151 ≤ (44488093022913/100000000000000 : ℝ)^4127
        have hw : |(52260269/100000000 : ℝ)|=(52260269/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085501741/2000000000 : ℝ)|^5151 ≤ (23319490254023/50000000000000 : ℝ)^4127
        have hw : |(1085501741/2000000000 : ℝ)|=(1085501741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-143610881/1000000000 : ℝ)|^5151 ≤ (8872926456811/100000000000000 : ℝ)^4127
        have hw : |(-143610881/1000000000 : ℝ)|=(143610881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_3 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2257023721/5000000000 : ℝ)*x 0 + (3960373697/10000000000 : ℝ)*x 1 + (1980187067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2257023721/5000000000 : ℝ)^5151 ≤ (9263952936959/25000000000000 : ℝ)^4127 := by
    have hnat : (2257023721 : ℕ)^5151*25000000000000^4127 ≤ 9263952936959^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257023721 5000000000 9263952936959 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3960373697/10000000000 : ℝ)^5151 ≤ (31472091954207/100000000000000 : ℝ)^4127 := by
    have hnat : (3960373697 : ℕ)^5151*100000000000000^4127 ≤ 31472091954207^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3960373697 10000000000 31472091954207 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1980187067/5000000000 : ℝ)^5151 ≤ (7868024072149/25000000000000 : ℝ)^4127 := by
    have hnat : (1980187067 : ℕ)^5151*25000000000000^4127 ≤ 7868024072149^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980187067 5000000000 7868024072149 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2257023721/5000000000 : ℝ), (3960373697/10000000000 : ℝ), (1980187067/5000000000 : ℝ)] ![(9263952936959/25000000000000 : ℝ), (31472091954207/100000000000000 : ℝ), (7868024072149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2257023721/5000000000 : ℝ)|^5151 ≤ (9263952936959/25000000000000 : ℝ)^4127
        have hw : |(2257023721/5000000000 : ℝ)|=(2257023721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3960373697/10000000000 : ℝ)|^5151 ≤ (31472091954207/100000000000000 : ℝ)^4127
        have hw : |(3960373697/10000000000 : ℝ)|=(3960373697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1980187067/5000000000 : ℝ)|^5151 ≤ (7868024072149/25000000000000 : ℝ)^4127
        have hw : |(1980187067/5000000000 : ℝ)|=(1980187067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_4 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1838840511/10000000000 : ℝ)*x 0 + (647034103/1250000000 : ℝ)*x 1 + (64703407/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1838840511/10000000000 : ℝ)^5151 ≤ (1509979975091/12500000000000 : ℝ)^4127 := by
    have hnat : (1838840511 : ℕ)^5151*12500000000000^4127 ≤ 1509979975091^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838840511 10000000000 1509979975091 12500000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647034103/1250000000 : ℝ)^5151 ≤ (4396008148859/10000000000000 : ℝ)^4127 := by
    have hnat : (647034103 : ℕ)^5151*10000000000000^4127 ≤ 4396008148859^4127*1250000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647034103 1250000000 4396008148859 10000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64703407/125000000 : ℝ)^5151 ≤ (21980039345119/50000000000000 : ℝ)^4127 := by
    have hnat : (64703407 : ℕ)^5151*50000000000000^4127 ≤ 21980039345119^4127*125000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64703407 125000000 21980039345119 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1838840511/10000000000 : ℝ), (647034103/1250000000 : ℝ), (64703407/125000000 : ℝ)] ![(1509979975091/12500000000000 : ℝ), (4396008148859/10000000000000 : ℝ), (21980039345119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1838840511/10000000000 : ℝ)|^5151 ≤ (1509979975091/12500000000000 : ℝ)^4127
        have hw : |(-1838840511/10000000000 : ℝ)|=(1838840511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647034103/1250000000 : ℝ)|^5151 ≤ (4396008148859/10000000000000 : ℝ)^4127
        have hw : |(647034103/1250000000 : ℝ)|=(647034103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(64703407/125000000 : ℝ)|^5151 ≤ (21980039345119/50000000000000 : ℝ)^4127
        have hw : |(64703407/125000000 : ℝ)|=(64703407/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_5 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53972031/100000000 : ℝ)*x 0 + (-61827277/400000000 : ℝ)*x 1 + (5176272919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53972031/100000000 : ℝ)^5151 ≤ (46314172156019/100000000000000 : ℝ)^4127 := by
    have hnat : (53972031 : ℕ)^5151*100000000000000^4127 ≤ 46314172156019^4127*100000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53972031 100000000 46314172156019 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61827277/400000000 : ℝ)^5151 ≤ (9725745332823/100000000000000 : ℝ)^4127 := by
    have hnat : (61827277 : ℕ)^5151*100000000000000^4127 ≤ 9725745332823^4127*400000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61827277 400000000 9725745332823 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176272919/10000000000 : ℝ)^5151 ≤ (10990020623893/25000000000000 : ℝ)^4127 := by
    have hnat : (5176272919 : ℕ)^5151*25000000000000^4127 ≤ 10990020623893^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176272919 10000000000 10990020623893 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53972031/100000000 : ℝ), (-61827277/400000000 : ℝ), (5176272919/10000000000 : ℝ)] ![(46314172156019/100000000000000 : ℝ), (9725745332823/100000000000000 : ℝ), (10990020623893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53972031/100000000 : ℝ)|^5151 ≤ (46314172156019/100000000000000 : ℝ)^4127
        have hw : |(53972031/100000000 : ℝ)|=(53972031/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-61827277/400000000 : ℝ)|^5151 ≤ (9725745332823/100000000000000 : ℝ)^4127
        have hw : |(-61827277/400000000 : ℝ)|=(61827277/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176272919/10000000000 : ℝ)|^5151 ≤ (10990020623893/25000000000000 : ℝ)^4127
        have hw : |(5176272919/10000000000 : ℝ)|=(5176272919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_6 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698601681/5000000000 : ℝ)*x 0 + (5176272709/10000000000 : ℝ)*x 1 + (-30913637/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698601681/5000000000 : ℝ)^5151 ≤ (46314174962121/100000000000000 : ℝ)^4127 := by
    have hnat : (2698601681 : ℕ)^5151*100000000000000^4127 ≤ 46314174962121^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698601681 5000000000 46314174962121 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176272709/10000000000 : ℝ)^5151 ≤ (43960080269611/100000000000000 : ℝ)^4127 := by
    have hnat : (5176272709 : ℕ)^5151*100000000000000^4127 ≤ 43960080269611^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176272709 10000000000 43960080269611 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30913637/200000000 : ℝ)^5151 ≤ (1215718092977/12500000000000 : ℝ)^4127 := by
    have hnat : (30913637 : ℕ)^5151*12500000000000^4127 ≤ 1215718092977^4127*200000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30913637 200000000 1215718092977 12500000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698601681/5000000000 : ℝ), (5176272709/10000000000 : ℝ), (-30913637/200000000 : ℝ)] ![(46314174962121/100000000000000 : ℝ), (43960080269611/100000000000000 : ℝ), (1215718092977/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698601681/5000000000 : ℝ)|^5151 ≤ (46314174962121/100000000000000 : ℝ)^4127
        have hw : |(2698601681/5000000000 : ℝ)|=(2698601681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176272709/10000000000 : ℝ)|^5151 ≤ (43960080269611/100000000000000 : ℝ)^4127
        have hw : |(5176272709/10000000000 : ℝ)|=(5176272709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30913637/200000000 : ℝ)|^5151 ≤ (1215718092977/12500000000000 : ℝ)^4127
        have hw : |(-30913637/200000000 : ℝ)|=(30913637/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_7 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1865542893/5000000000 : ℝ)*x 0 + (4350995599/10000000000 : ℝ)*x 1 + (4350995139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1865542893/5000000000 : ℝ)^5151 ≤ (14607237430051/50000000000000 : ℝ)^4127 := by
    have hnat : (1865542893 : ℕ)^5151*50000000000000^4127 ≤ 14607237430051^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865542893 5000000000 14607237430051 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4350995599/10000000000 : ℝ)^5151 ≤ (884819122429/2500000000000 : ℝ)^4127 := by
    have hnat : (4350995599 : ℕ)^5151*2500000000000^4127 ≤ 884819122429^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350995599 10000000000 884819122429 2500000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4350995139/10000000000 : ℝ)^5151 ≤ (4424095028363/12500000000000 : ℝ)^4127 := by
    have hnat : (4350995139 : ℕ)^5151*12500000000000^4127 ≤ 4424095028363^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350995139 10000000000 4424095028363 12500000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1865542893/5000000000 : ℝ), (4350995599/10000000000 : ℝ), (4350995139/10000000000 : ℝ)] ![(14607237430051/50000000000000 : ℝ), (884819122429/2500000000000 : ℝ), (4424095028363/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1865542893/5000000000 : ℝ)|^5151 ≤ (14607237430051/50000000000000 : ℝ)^4127
        have hw : |(1865542893/5000000000 : ℝ)|=(1865542893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4350995599/10000000000 : ℝ)|^5151 ≤ (884819122429/2500000000000 : ℝ)^4127
        have hw : |(4350995599/10000000000 : ℝ)|=(4350995599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4350995139/10000000000 : ℝ)|^5151 ≤ (4424095028363/12500000000000 : ℝ)^4127
        have hw : |(4350995139/10000000000 : ℝ)|=(4350995139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_8 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-338190787/2000000000 : ℝ)*x 0 + (4991854333/10000000000 : ℝ)*x 1 + (1367761033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338190787/2000000000 : ℝ)^5151 ≤ (10879631724947/100000000000000 : ℝ)^4127 := by
    have hnat : (338190787 : ℕ)^5151*100000000000000^4127 ≤ 10879631724947^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338190787 2000000000 10879631724947 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4991854333/10000000000 : ℝ)^5151 ≤ (21006998825527/50000000000000 : ℝ)^4127 := by
    have hnat : (4991854333 : ℕ)^5151*50000000000000^4127 ≤ 21006998825527^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4991854333 10000000000 21006998825527 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367761033/2500000000 : ℝ)^5151 ≤ (47106370605581/100000000000000 : ℝ)^4127 := by
    have hnat : (1367761033 : ℕ)^5151*100000000000000^4127 ≤ 47106370605581^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367761033 2500000000 47106370605581 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-338190787/2000000000 : ℝ), (4991854333/10000000000 : ℝ), (1367761033/2500000000 : ℝ)] ![(10879631724947/100000000000000 : ℝ), (21006998825527/50000000000000 : ℝ), (47106370605581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-338190787/2000000000 : ℝ)|^5151 ≤ (10879631724947/100000000000000 : ℝ)^4127
        have hw : |(-338190787/2000000000 : ℝ)|=(338190787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4991854333/10000000000 : ℝ)|^5151 ≤ (21006998825527/50000000000000 : ℝ)^4127
        have hw : |(4991854333/10000000000 : ℝ)|=(4991854333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367761033/2500000000 : ℝ)|^5151 ≤ (47106370605581/100000000000000 : ℝ)^4127
        have hw : |(1367761033/2500000000 : ℝ)|=(1367761033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_9 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299094827/2500000000 : ℝ)*x 0 + (-1416290901/10000000000 : ℝ)*x 1 + (5471040059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299094827/2500000000 : ℝ)^5151 ≤ (22086654582801/50000000000000 : ℝ)^4127 := by
    have hnat : (1299094827 : ℕ)^5151*50000000000000^4127 ≤ 22086654582801^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299094827 2500000000 22086654582801 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1416290901/10000000000 : ℝ)^5151 ≤ (8720363990243/100000000000000 : ℝ)^4127 := by
    have hnat : (1416290901 : ℕ)^5151*100000000000000^4127 ≤ 8720363990243^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1416290901 10000000000 8720363990243 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471040059/10000000000 : ℝ)^5151 ≤ (9421265367029/20000000000000 : ℝ)^4127 := by
    have hnat : (5471040059 : ℕ)^5151*20000000000000^4127 ≤ 9421265367029^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471040059 10000000000 9421265367029 20000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299094827/2500000000 : ℝ), (-1416290901/10000000000 : ℝ), (5471040059/10000000000 : ℝ)] ![(22086654582801/50000000000000 : ℝ), (8720363990243/100000000000000 : ℝ), (9421265367029/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299094827/2500000000 : ℝ)|^5151 ≤ (22086654582801/50000000000000 : ℝ)^4127
        have hw : |(1299094827/2500000000 : ℝ)|=(1299094827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1416290901/10000000000 : ℝ)|^5151 ≤ (8720363990243/100000000000000 : ℝ)^4127
        have hw : |(-1416290901/10000000000 : ℝ)|=(1416290901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471040059/10000000000 : ℝ)|^5151 ≤ (9421265367029/20000000000000 : ℝ)^4127
        have hw : |(5471040059/10000000000 : ℝ)|=(5471040059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_10 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196377831/10000000000 : ℝ)*x 0 + (2735521249/5000000000 : ℝ)*x 1 + (-1416289529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196377831/10000000000 : ℝ)^5151 ≤ (11043323373651/25000000000000 : ℝ)^4127 := by
    have hnat : (5196377831 : ℕ)^5151*25000000000000^4127 ≤ 11043323373651^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196377831 10000000000 11043323373651 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735521249/5000000000 : ℝ)^5151 ≤ (23553176522911/50000000000000 : ℝ)^4127 := by
    have hnat : (2735521249 : ℕ)^5151*50000000000000^4127 ≤ 23553176522911^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735521249 5000000000 23553176522911 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1416289529/10000000000 : ℝ)^5151 ≤ (8720353446537/100000000000000 : ℝ)^4127 := by
    have hnat : (1416289529 : ℕ)^5151*100000000000000^4127 ≤ 8720353446537^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1416289529 10000000000 8720353446537 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196377831/10000000000 : ℝ), (2735521249/5000000000 : ℝ), (-1416289529/10000000000 : ℝ)] ![(11043323373651/25000000000000 : ℝ), (23553176522911/50000000000000 : ℝ), (8720353446537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196377831/10000000000 : ℝ)|^5151 ≤ (11043323373651/25000000000000 : ℝ)^4127
        have hw : |(5196377831/10000000000 : ℝ)|=(5196377831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735521249/5000000000 : ℝ)|^5151 ≤ (23553176522911/50000000000000 : ℝ)^4127
        have hw : |(2735521249/5000000000 : ℝ)|=(2735521249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1416289529/10000000000 : ℝ)|^5151 ≤ (8720353446537/100000000000000 : ℝ)^4127
        have hw : |(-1416289529/10000000000 : ℝ)|=(1416289529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_11 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2322343493/5000000000 : ℝ)*x 0 + (1946256023/5000000000 : ℝ)*x 1 + (3892514177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2322343493/5000000000 : ℝ)^5151 ≤ (19199547070921/50000000000000 : ℝ)^4127 := by
    have hnat : (2322343493 : ℕ)^5151*50000000000000^4127 ≤ 19199547070921^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2322343493 5000000000 19199547070921 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1946256023/5000000000 : ℝ)^5151 ≤ (3080044239473/10000000000000 : ℝ)^4127 := by
    have hnat : (1946256023 : ℕ)^5151*10000000000000^4127 ≤ 3080044239473^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946256023 5000000000 3080044239473 10000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3892514177/10000000000 : ℝ)^5151 ≤ (3850057930079/12500000000000 : ℝ)^4127 := by
    have hnat : (3892514177 : ℕ)^5151*12500000000000^4127 ≤ 3850057930079^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3892514177 10000000000 3850057930079 12500000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2322343493/5000000000 : ℝ), (1946256023/5000000000 : ℝ), (3892514177/10000000000 : ℝ)] ![(19199547070921/50000000000000 : ℝ), (3080044239473/10000000000000 : ℝ), (3850057930079/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2322343493/5000000000 : ℝ)|^5151 ≤ (19199547070921/50000000000000 : ℝ)^4127
        have hw : |(2322343493/5000000000 : ℝ)|=(2322343493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1946256023/5000000000 : ℝ)|^5151 ≤ (3080044239473/10000000000000 : ℝ)^4127
        have hw : |(1946256023/5000000000 : ℝ)|=(1946256023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3892514177/10000000000 : ℝ)|^5151 ≤ (3850057930079/12500000000000 : ℝ)^4127
        have hw : |(3892514177/10000000000 : ℝ)|=(3892514177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_12 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-646375853/5000000000 : ℝ)*x 0 + (1400698389/2500000000 : ℝ)*x 1 + (1030195123/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646375853/5000000000 : ℝ)^5151 ≤ (155629657181/2000000000000 : ℝ)^4127 := by
    have hnat : (646375853 : ℕ)^5151*2000000000000^4127 ≤ 155629657181^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646375853 5000000000 155629657181 2000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1400698389/2500000000 : ℝ)^5151 ≤ (12131604668271/25000000000000 : ℝ)^4127 := by
    have hnat : (1400698389 : ℕ)^5151*25000000000000^4127 ≤ 12131604668271^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400698389 2500000000 12131604668271 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030195123/2000000000 : ℝ)^5151 ≤ (43692098453129/100000000000000 : ℝ)^4127 := by
    have hnat : (1030195123 : ℕ)^5151*100000000000000^4127 ≤ 43692098453129^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030195123 2000000000 43692098453129 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-646375853/5000000000 : ℝ), (1400698389/2500000000 : ℝ), (1030195123/2000000000 : ℝ)] ![(155629657181/2000000000000 : ℝ), (12131604668271/25000000000000 : ℝ), (43692098453129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-646375853/5000000000 : ℝ)|^5151 ≤ (155629657181/2000000000000 : ℝ)^4127
        have hw : |(-646375853/5000000000 : ℝ)|=(646375853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1400698389/2500000000 : ℝ)|^5151 ≤ (12131604668271/25000000000000 : ℝ)^4127
        have hw : |(1400698389/2500000000 : ℝ)|=(1400698389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030195123/2000000000 : ℝ)|^5151 ≤ (43692098453129/100000000000000 : ℝ)^4127
        have hw : |(1030195123/2000000000 : ℝ)|=(1030195123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_13 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5414465819/10000000000 : ℝ)*x 0 + (-311248681/2000000000 : ℝ)*x 1 + (5150976319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414465819/10000000000 : ℝ)^5151 ≤ (46499134612399/100000000000000 : ℝ)^4127 := by
    have hnat : (5414465819 : ℕ)^5151*100000000000000^4127 ≤ 46499134612399^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414465819 10000000000 46499134612399 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (311248681/2000000000 : ℝ)^5151 ≤ (4904379728731/50000000000000 : ℝ)^4127 := by
    have hnat : (311248681 : ℕ)^5151*50000000000000^4127 ≤ 4904379728731^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311248681 2000000000 4904379728731 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5150976319/10000000000 : ℝ)^5151 ≤ (1365378309573/3125000000000 : ℝ)^4127 := by
    have hnat : (5150976319 : ℕ)^5151*3125000000000^4127 ≤ 1365378309573^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150976319 10000000000 1365378309573 3125000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414465819/10000000000 : ℝ), (-311248681/2000000000 : ℝ), (5150976319/10000000000 : ℝ)] ![(46499134612399/100000000000000 : ℝ), (4904379728731/50000000000000 : ℝ), (1365378309573/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414465819/10000000000 : ℝ)|^5151 ≤ (46499134612399/100000000000000 : ℝ)^4127
        have hw : |(5414465819/10000000000 : ℝ)|=(5414465819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-311248681/2000000000 : ℝ)|^5151 ≤ (4904379728731/50000000000000 : ℝ)^4127
        have hw : |(-311248681/2000000000 : ℝ)|=(311248681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5150976319/10000000000 : ℝ)|^5151 ≤ (1365378309573/3125000000000 : ℝ)^4127
        have hw : |(5150976319/10000000000 : ℝ)|=(5150976319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_14 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (541446731/1000000000 : ℝ)*x 0 + (5150973771/10000000000 : ℝ)*x 1 + (-389061201/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541446731/1000000000 : ℝ)^5151 ≤ (46499150594137/100000000000000 : ℝ)^4127 := by
    have hnat : (541446731 : ℕ)^5151*100000000000000^4127 ≤ 46499150594137^4127*1000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541446731 1000000000 46499150594137 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150973771/10000000000 : ℝ)^5151 ≤ (43692078930811/100000000000000 : ℝ)^4127 := by
    have hnat : (5150973771 : ℕ)^5151*100000000000000^4127 ≤ 43692078930811^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150973771 10000000000 43692078930811 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389061201/2500000000 : ℝ)^5151 ≤ (9808770463003/100000000000000 : ℝ)^4127 := by
    have hnat : (389061201 : ℕ)^5151*100000000000000^4127 ≤ 9808770463003^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389061201 2500000000 9808770463003 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541446731/1000000000 : ℝ), (5150973771/10000000000 : ℝ), (-389061201/2500000000 : ℝ)] ![(46499150594137/100000000000000 : ℝ), (43692078930811/100000000000000 : ℝ), (9808770463003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541446731/1000000000 : ℝ)|^5151 ≤ (46499150594137/100000000000000 : ℝ)^4127
        have hw : |(541446731/1000000000 : ℝ)|=(541446731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150973771/10000000000 : ℝ)|^5151 ≤ (43692078930811/100000000000000 : ℝ)^4127
        have hw : |(5150973771/10000000000 : ℝ)|=(5150973771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-389061201/2500000000 : ℝ)|^5151 ≤ (9808770463003/100000000000000 : ℝ)^4127
        have hw : |(-389061201/2500000000 : ℝ)|=(389061201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_box_15 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (729853203/2000000000 : ℝ)*x 0 + (439022467/1000000000 : ℝ)*x 1 + (878044233/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (729853203/2000000000 : ℝ)^5151 ≤ (1420852618459/5000000000000 : ℝ)^4127 := by
    have hnat : (729853203 : ℕ)^5151*5000000000000^4127 ≤ 1420852618459^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729853203 2000000000 1420852618459 5000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (439022467/1000000000 : ℝ)^5151 ≤ (35791491642371/100000000000000 : ℝ)^4127 := by
    have hnat : (439022467 : ℕ)^5151*100000000000000^4127 ≤ 35791491642371^4127*1000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439022467 1000000000 35791491642371 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (878044233/2000000000 : ℝ)^5151 ≤ (35791455977709/100000000000000 : ℝ)^4127 := by
    have hnat : (878044233 : ℕ)^5151*100000000000000^4127 ≤ 35791455977709^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878044233 2000000000 35791455977709 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(729853203/2000000000 : ℝ), (439022467/1000000000 : ℝ), (878044233/2000000000 : ℝ)] ![(1420852618459/5000000000000 : ℝ), (35791491642371/100000000000000 : ℝ), (35791455977709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(729853203/2000000000 : ℝ)|^5151 ≤ (1420852618459/5000000000000 : ℝ)^4127
        have hw : |(729853203/2000000000 : ℝ)|=(729853203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(439022467/1000000000 : ℝ)|^5151 ≤ (35791491642371/100000000000000 : ℝ)^4127
        have hw : |(439022467/1000000000 : ℝ)|=(439022467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(878044233/2000000000 : ℝ)|^5151 ≤ (35791455977709/100000000000000 : ℝ)^4127
        have hw : |(878044233/2000000000 : ℝ)|=(878044233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1691_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17227/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9841/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66581/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(28977/50000 : ℝ) ∧ (2021/2500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90147/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17227/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9841/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17227/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9841/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17227/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9841/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17227/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9841/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17227/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9841/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17227/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9841/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9841/100000 : ℝ) ^ (5143/1024 : ℝ) ≤ (54759426804569/6250000000000000000 : ℝ) := by
    have hpowers : (9841/100000 : ℝ)^5143 ≤ (54759426804569/6250000000000000000 : ℝ)^1024 := by
      have hnat : (9841 : ℕ)^5143*6250000000000000000^1024 ≤ 54759426804569^1024*100000^5143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9841 100000 54759426804569 6250000000000000000 5143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9841/100000 : ℝ)) (X := (54759426804569/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17227/100000 : ℝ) ^ (5143/1024 : ℝ) ≤ (14584542869123673/100000000000000000000 : ℝ) := by
    have hpowers : (17227/100000 : ℝ)^5143 ≤ (14584542869123673/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17227 : ℕ)^5143*100000000000000000000^1024 ≤ 14584542869123673^1024*100000^5143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17227 100000 14584542869123673 100000000000000000000 5143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17227/100000 : ℝ)) (X := (14584542869123673/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125054759426804569/3125000000000000000 : ℝ) ≤ (2500008722264761/2500000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (3125054759426804569/3125000000000000000 : ℝ)^1024 ≤ (2500008722264761/2500000000000000 : ℝ)^5143 := by
      have hnat : (3125054759426804569 : ℕ)^1024*2500000000000000^5143 ≤ 2500008722264761^5143*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125054759426804569 3125000000000000000 2500008722264761 2500000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500008722264761/2500000000000000 : ℝ)) (X := (3125054759426804569/3125000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100015460693697996777/100000000000000000000 : ℝ) ≤ (10000307811982573/10000000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (100015460693697996777/100000000000000000000 : ℝ)^1024 ≤ (10000307811982573/10000000000000000 : ℝ)^5143 := by
      have hnat : (100015460693697996777 : ℕ)^1024*10000000000000000^5143 ≤ 10000307811982573^5143*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015460693697996777 100000000000000000000 10000307811982573 10000000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000307811982573/10000000000000000 : ℝ)) (X := (100015460693697996777/100000000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014584542869123673/50000000000000000000 : ℝ) ≤ (5000290367453051/5000000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (50014584542869123673/50000000000000000000 : ℝ)^1024 ≤ (5000290367453051/5000000000000000 : ℝ)^5143 := by
      have hnat : (50014584542869123673 : ℕ)^1024*5000000000000000^5143 ≤ 5000290367453051^5143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014584542869123673 50000000000000000000 5000290367453051 5000000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000290367453051/5000000000000000 : ℝ)) (X := (50014584542869123673/50000000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(54759426804569/6250000000000000000 : ℝ) ≤ ((12309147670268200201/12310000000000000000 : ℝ)+2*(90974307843/246200000000000 : ℝ)*(9841/100000 : ℝ))^(5143/1024 : ℝ) := by
    rw [show (12309147670268200201/12310000000000000000 : ℝ)+2*(90974307843/246200000000000 : ℝ)*(9841/100000 : ℝ)=(2500008722264761/2500000000000000 : ℝ) by norm_num, show 1+2*(54759426804569/6250000000000000000 : ℝ)=(3125054759426804569/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14584542869123673/100000000000000000000 : ℝ)+(54759426804569/6250000000000000000 : ℝ) ≤ ((12309147670268200201/12310000000000000000 : ℝ)+(90974307843/246200000000000 : ℝ)*((17227/100000 : ℝ)+(9841/100000 : ℝ)))^(5143/1024 : ℝ) := by
    rw [show (12309147670268200201/12310000000000000000 : ℝ)+(90974307843/246200000000000 : ℝ)*((17227/100000 : ℝ)+(9841/100000 : ℝ))=(10000307811982573/10000000000000000 : ℝ) by norm_num, show 1+(14584542869123673/100000000000000000000 : ℝ)+(54759426804569/6250000000000000000 : ℝ)=(100015460693697996777/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14584542869123673/100000000000000000000 : ℝ) ≤ ((12309147670268200201/12310000000000000000 : ℝ)+2*(90974307843/246200000000000 : ℝ)*(17227/100000 : ℝ))^(5143/1024 : ℝ) := by
    rw [show (12309147670268200201/12310000000000000000 : ℝ)+2*(90974307843/246200000000000 : ℝ)*(17227/100000 : ℝ)=(5000290367453051/5000000000000000 : ℝ) by norm_num, show 1+2*(14584542869123673/100000000000000000000 : ℝ)=(50014584542869123673/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12309147670268200201/12310000000000000000 : ℝ)*(X 1 0+X 2 0)+(90974307843/246200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (9841/100000 : ℝ)) (hi := (17227/100000 : ℝ)) (c := (12309147670268200201/12310000000000000000 : ℝ)) (alpha := (90974307843/246200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12309147670268200201/12310000000000000000 : ℝ)*(X 0 1+X 2 1)+(90974307843/246200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (9841/100000 : ℝ)) (hi := (17227/100000 : ℝ)) (c := (12309147670268200201/12310000000000000000 : ℝ)) (alpha := (90974307843/246200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12309147670268200201/12310000000000000000 : ℝ)*(X 0 2+X 1 2)+(90974307843/246200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (9841/100000 : ℝ)) (hi := (17227/100000 : ℝ)) (c := (12309147670268200201/12310000000000000000 : ℝ)) (alpha := (90974307843/246200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-45988529/400000000 : ℝ)*X 0 0+(339219279/625000000 : ℝ)*X 0 1+(2713754487/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5226026771/10000000000 : ℝ)*X 1 0+(-143610891/1000000000 : ℝ)*X 1 1+(135687719/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((52260269/100000000 : ℝ)*X 2 0+(1085501741/2000000000 : ℝ)*X 2 1+(-143610881/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2257023721/5000000000 : ℝ)*X 0 0+(3960373697/10000000000 : ℝ)*X 0 1+(1980187067/5000000000 : ℝ)*X 0 2+(2257023721/5000000000 : ℝ)*X 1 0+(3960373697/10000000000 : ℝ)*X 1 1+(1980187067/5000000000 : ℝ)*X 1 2+(2257023721/5000000000 : ℝ)*X 2 0+(3960373697/10000000000 : ℝ)*X 2 1+(1980187067/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1838840511/10000000000 : ℝ)*X 0 0+(647034103/1250000000 : ℝ)*X 0 1+(64703407/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((53972031/100000000 : ℝ)*X 1 0+(-61827277/400000000 : ℝ)*X 1 1+(5176272919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2698601681/5000000000 : ℝ)*X 2 0+(5176272709/10000000000 : ℝ)*X 2 1+(-30913637/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1865542893/5000000000 : ℝ)*X 0 0+(4350995599/10000000000 : ℝ)*X 0 1+(4350995139/10000000000 : ℝ)*X 0 2+(1865542893/5000000000 : ℝ)*X 1 0+(4350995599/10000000000 : ℝ)*X 1 1+(4350995139/10000000000 : ℝ)*X 1 2+(1865542893/5000000000 : ℝ)*X 2 0+(4350995599/10000000000 : ℝ)*X 2 1+(4350995139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-338190787/2000000000 : ℝ)*X 0 0+(4991854333/10000000000 : ℝ)*X 0 1+(1367761033/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1299094827/2500000000 : ℝ)*X 1 0+(-1416290901/10000000000 : ℝ)*X 1 1+(5471040059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196377831/10000000000 : ℝ)*X 2 0+(2735521249/5000000000 : ℝ)*X 2 1+(-1416289529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2322343493/5000000000 : ℝ)*X 0 0+(1946256023/5000000000 : ℝ)*X 0 1+(3892514177/10000000000 : ℝ)*X 0 2+(2322343493/5000000000 : ℝ)*X 1 0+(1946256023/5000000000 : ℝ)*X 1 1+(3892514177/10000000000 : ℝ)*X 1 2+(2322343493/5000000000 : ℝ)*X 2 0+(1946256023/5000000000 : ℝ)*X 2 1+(3892514177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-646375853/5000000000 : ℝ)*X 0 0+(1400698389/2500000000 : ℝ)*X 0 1+(1030195123/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5414465819/10000000000 : ℝ)*X 1 0+(-311248681/2000000000 : ℝ)*X 1 1+(5150976319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((541446731/1000000000 : ℝ)*X 2 0+(5150973771/10000000000 : ℝ)*X 2 1+(-389061201/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((729853203/2000000000 : ℝ)*X 0 0+(439022467/1000000000 : ℝ)*X 0 1+(878044233/2000000000 : ℝ)*X 0 2+(729853203/2000000000 : ℝ)*X 1 0+(439022467/1000000000 : ℝ)*X 1 1+(878044233/2000000000 : ℝ)*X 1 2+(729853203/2000000000 : ℝ)*X 2 0+(439022467/1000000000 : ℝ)*X 2 1+(878044233/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66581/100000 : ℝ) ≤ (-8195772374992108623798276183/12310000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1073437/10000000000000 : ℝ)*(lower0) + (2728059/3125000000000 : ℝ)*(lower2) + (47070197/100000000000000 : ℝ)*(lower4) + (1308120132539039/100000000000000 : ℝ)*(major0) + (1308120132539039/100000000000000 : ℝ)*(major1) + (1308120132539039/100000000000000 : ℝ)*(major2) + (1945185625901687/100000000000000 : ℝ)*(sp4) + (1945181045888809/100000000000000 : ℝ)*(sp5) + (243148408151279/12500000000000 : ℝ)*(sp6) + (346618701674851/50000000000000 : ℝ)*(sp7) + (1819810871/100000000000000 : ℝ)*(sp8) + (1599955937/25000000000000 : ℝ)*(sp13) + (90251163/50000000000000 : ℝ)*(sp14) + (4069197981/50000000000000 : ℝ)*(sp15) + (676997599361/97656250000 : ℝ)*(f.failure) + (1945187445712557/100000000000000 : ℝ)*(f.sum) + (430375165957277/12310000000000000000000000000 : ℝ)*base65 + (5452489103995003161/1231000000000000000000000000000000 : ℝ)*base68 + (4126271045956003161/1231000000000000000000000000000000 : ℝ)*base70 + (36968149373109996839/1231000000000000000000000000000000 : ℝ)*base71 + (26422675827247/12310000000000000000000000000 : ℝ)*base73 + (1753576583722996839/1231000000000000000000000000000000 : ℝ)*base75 + (121136583217996839/1231000000000000000000000000000000 : ℝ)*base77 + (7082261340388003161/1231000000000000000000000000000000 : ℝ)*base80 + (38540070723637/12310000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (298071/39062500000000000000 : ℝ)*base90 + (298071/39062500000000000000 : ℝ)*base92 + (298071/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (28977/50000 : ℝ) ≤ (356721287816292158496326343230019/615500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10106993/25000000000000 : ℝ)*(lower0) + (19182179/50000000000000 : ℝ)*(lower1) + (2260619/3125000000000 : ℝ)*(lower3) + (1407449544479309/100000000000000 : ℝ)*(major0) + (1407449544479309/100000000000000 : ℝ)*(major1) + (1407449544479309/100000000000000 : ℝ)*(major2) + (256211664439953/12500000000000 : ℝ)*(sp0) + (2049693580569543/100000000000000 : ℝ)*(sp1) + (2049691512952463/100000000000000 : ℝ)*(sp2) + (93235569984147/12500000000000 : ℝ)*(sp3) + (505682259/50000000000000 : ℝ)*(sp5) + (1156332731/100000000000000 : ℝ)*(sp7) + (1539490799/50000000000000 : ℝ)*(sp10) + (1276414437/100000000000000 : ℝ)*(sp12) + (745885716205907/100000000000000 : ℝ)*(f.failure) + (2049694591934061/100000000000000 : ℝ)*(f.sum) + (9951449146673/12310000000000000000000000000 : ℝ)*base66 + (4495540766819491109/1231000000000000000000000000000000 : ℝ)*base67 + (24406084770894491109/1231000000000000000000000000000000 : ℝ)*base69 + (1246992378797491109/1231000000000000000000000000000000 : ℝ)*base71 + (19525758762423/12310000000000000000000000000 : ℝ)*base74 + (7383170260773491109/1231000000000000000000000000000000 : ℝ)*base75 + (2430516174062491109/1231000000000000000000000000000000 : ℝ)*base77 + (1818636835578491109/1231000000000000000000000000000000 : ℝ)*base79 + (30983913656023/12310000000000000000000000000 : ℝ)*base82 + (4522569/5000000000000000000000 : ℝ)*base90 + (4522569/5000000000000000000000 : ℝ)*base92 + (4522569/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (2021/2500 : ℝ) ≤ (497586131313888905654756963139567/615500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6028421/10000000000000 : ℝ)*(upper2) + (4595783/1562500000000 : ℝ)*(lower3) + (5582347/50000000000000 : ℝ)*(lower5) + (1437938182321537/100000000000000 : ℝ)*(major0) + (1437938182321537/100000000000000 : ℝ)*(major1) + (1437938182321537/100000000000000 : ℝ)*(major2) + (16725569181/20000000000000 : ℝ)*(sp2) + (13756779897/100000000000000 : ℝ)*(sp3) + (8745402051/100000000000000 : ℝ)*(sp4) + (260858429710799/12500000000000 : ℝ)*(sp8) + (2086885495743193/100000000000000 : ℝ)*(sp9) + (260850233487161/12500000000000 : ℝ)*(sp10) + (762029582668913/100000000000000 : ℝ)*(sp11) + (37250619/400000000000 : ℝ)*(sp12) + (76204333944881/10000000000000 : ℝ)*(f.failure) + (2086885495743193/100000000000000 : ℝ)*(f.sum) + (70397254943281/12310000000000000000000000000 : ℝ)*base65 + (118177198427578937/1231000000000000000000000000000000 : ℝ)*base67 + (3656104945061578937/1231000000000000000000000000000000 : ℝ)*base69 + (3288118689188578937/1231000000000000000000000000000000 : ℝ)*base71 + (929503430649/12310000000000000000000000000 : ℝ)*base74 + (1995763125638578937/1231000000000000000000000000000000 : ℝ)*base75 + (7786172520484578937/1231000000000000000000000000000000 : ℝ)*base77 + (4014589006068578937/1231000000000000000000000000000000 : ℝ)*base79 + (59093624697621/12310000000000000000000000000 : ℝ)*base81 + (4671427/500000000000000000000 : ℝ)*base90 + (4671427/500000000000000000000 : ℝ)*base92 + (4671427/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-90147/100000 : ℝ) ≤ (-55483784938985707337193868624689/61550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75349427/50000000000000 : ℝ)*(upper1) + (3181519/100000000000000 : ℝ)*(lower2) + (291804737/100000000000000 : ℝ)*(upper3) + (56971447/100000000000000 : ℝ)*(upper5) + (148515141151037/10000000000000 : ℝ)*(major0) + (148515141151037/10000000000000 : ℝ)*(major1) + (148515141151037/10000000000000 : ℝ)*(major2) + (2907366299/50000000000000 : ℝ)*(sp4) + (23663440211/12500000000000 : ℝ)*(sp6) + (5264947061/20000000000000 : ℝ)*(sp7) + (442656167638851/20000000000000 : ℝ)*(sp12) + (2213286652926853/100000000000000 : ℝ)*(sp13) + (1106548672702583/50000000000000 : ℝ)*(sp14) + (787037928184997/100000000000000 : ℝ)*(sp15) + (393532126460151/50000000000000 : ℝ)*(f.failure) + (2213286652926853/100000000000000 : ℝ)*(f.sum) + (425575828351/307750000000000000000000000 : ℝ)*base65 + (698400247341608437/123100000000000000000000000000000 : ℝ)*base67 + (609772421421191563/123100000000000000000000000000000 : ℝ)*base70 + (75261513809108437/123100000000000000000000000000000 : ℝ)*base71 + (3940237748371/1231000000000000000000000000 : ℝ)*base73 + (971586883007391563/123100000000000000000000000000000 : ℝ)*base76 + (478430088088791563/123100000000000000000000000000000 : ℝ)*base78 + (903053968540991563/123100000000000000000000000000000 : ℝ)*base80 + (176079108509/49240000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (19657483/2500000000000000000000 : ℝ)*base89 + (19657483/2500000000000000000000 : ℝ)*base91 + (19657483/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1691_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17227/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9841/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66581/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(28977/50000 : ℝ) else (2021/2500 : ℝ) ≤ X j i ∧ X j i ≤ (90147/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1691_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1691_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (69/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4911/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66581/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(28977/50000 : ℝ) else (2021/2500 : ℝ) ≤ X j i ∧ X j i ≤ (90147/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1691_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1691_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1691_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (69/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4911/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66581/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(28977/50000 : ℝ) else (2021/2500 : ℝ) ≤ X j i ∧ X j i ≤ (90147/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1691_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
