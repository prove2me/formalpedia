-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1651_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:13:10.131864+00:00
-- url     : https://prove2.me/submissions/cb2f63ef-e570-4d8c-a29d-58db0b7de27b

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
theorem support_rectangle_w1651_s0_0 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1490903231/10000000000 : ℝ)*x 0 + (5784058627/10000000000 : ℝ)*x 1 + (2461119911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1490903231/10000000000 : ℝ)^4923 ≤ (1808844729057/20000000000000 : ℝ)^3899 := by
    have hnat : (1490903231 : ℕ)^4923*20000000000000^3899 ≤ 1808844729057^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1490903231 10000000000 1808844729057 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5784058627/10000000000 : ℝ)^4923 ≤ (25047103923271/50000000000000 : ℝ)^3899 := by
    have hnat : (5784058627 : ℕ)^4923*50000000000000^3899 ≤ 25047103923271^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5784058627 10000000000 25047103923271 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2461119911/5000000000 : ℝ)^4923 ≤ (20430784250139/50000000000000 : ℝ)^3899 := by
    have hnat : (2461119911 : ℕ)^4923*50000000000000^3899 ≤ 20430784250139^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2461119911 5000000000 20430784250139 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1490903231/10000000000 : ℝ), (5784058627/10000000000 : ℝ), (2461119911/5000000000 : ℝ)] ![(1808844729057/20000000000000 : ℝ), (25047103923271/50000000000000 : ℝ), (20430784250139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1490903231/10000000000 : ℝ)|^4923 ≤ (1808844729057/20000000000000 : ℝ)^3899
        have hw : |(-1490903231/10000000000 : ℝ)|=(1490903231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5784058627/10000000000 : ℝ)|^4923 ≤ (25047103923271/50000000000000 : ℝ)^3899
        have hw : |(5784058627/10000000000 : ℝ)|=(5784058627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2461119911/5000000000 : ℝ)|^4923 ≤ (20430784250139/50000000000000 : ℝ)^3899
        have hw : |(2461119911/5000000000 : ℝ)|=(2461119911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s0_1 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5437140329/10000000000 : ℝ)*x 0 + (-1963884833/10000000000 : ℝ)*x 1 + (4922240221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5437140329/10000000000 : ℝ)^4923 ≤ (23165438727413/50000000000000 : ℝ)^3899 := by
    have hnat : (5437140329 : ℕ)^4923*50000000000000^3899 ≤ 23165438727413^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437140329 10000000000 23165438727413 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1963884833/10000000000 : ℝ)^4923 ≤ (2561509968701/20000000000000 : ℝ)^3899 := by
    have hnat : (1963884833 : ℕ)^4923*20000000000000^3899 ≤ 2561509968701^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963884833 10000000000 2561509968701 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4922240221/10000000000 : ℝ)^4923 ≤ (40861572682449/100000000000000 : ℝ)^3899 := by
    have hnat : (4922240221 : ℕ)^4923*100000000000000^3899 ≤ 40861572682449^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4922240221 10000000000 40861572682449 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5437140329/10000000000 : ℝ), (-1963884833/10000000000 : ℝ), (4922240221/10000000000 : ℝ)] ![(23165438727413/50000000000000 : ℝ), (2561509968701/20000000000000 : ℝ), (40861572682449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5437140329/10000000000 : ℝ)|^4923 ≤ (23165438727413/50000000000000 : ℝ)^3899
        have hw : |(5437140329/10000000000 : ℝ)|=(5437140329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1963884833/10000000000 : ℝ)|^4923 ≤ (2561509968701/20000000000000 : ℝ)^3899
        have hw : |(-1963884833/10000000000 : ℝ)|=(1963884833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4922240221/10000000000 : ℝ)|^4923 ≤ (40861572682449/100000000000000 : ℝ)^3899
        have hw : |(4922240221/10000000000 : ℝ)|=(4922240221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s0_2 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5437141003/10000000000 : ℝ)*x 0 + (2461119831/5000000000 : ℝ)*x 1 + (-245485583/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5437141003/10000000000 : ℝ)^4923 ≤ (4633088470647/10000000000000 : ℝ)^3899 := by
    have hnat : (5437141003 : ℕ)^4923*10000000000000^3899 ≤ 4633088470647^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437141003 10000000000 4633088470647 10000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2461119831/5000000000 : ℝ)^4923 ≤ (40861566823217/100000000000000 : ℝ)^3899 := by
    have hnat : (2461119831 : ℕ)^4923*100000000000000^3899 ≤ 40861566823217^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2461119831 5000000000 40861566823217 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245485583/1250000000 : ℝ)^4923 ≤ (3201887112977/25000000000000 : ℝ)^3899 := by
    have hnat : (245485583 : ℕ)^4923*25000000000000^3899 ≤ 3201887112977^3899*1250000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245485583 1250000000 3201887112977 25000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5437141003/10000000000 : ℝ), (2461119831/5000000000 : ℝ), (-245485583/1250000000 : ℝ)] ![(4633088470647/10000000000000 : ℝ), (40861566823217/100000000000000 : ℝ), (3201887112977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5437141003/10000000000 : ℝ)|^4923 ≤ (4633088470647/10000000000000 : ℝ)^3899
        have hw : |(5437141003/10000000000 : ℝ)|=(5437141003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2461119831/5000000000 : ℝ)|^4923 ≤ (40861566823217/100000000000000 : ℝ)^3899
        have hw : |(2461119831/5000000000 : ℝ)|=(2461119831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245485583/1250000000 : ℝ)|^4923 ≤ (3201887112977/25000000000000 : ℝ)^3899
        have hw : |(-245485583/1250000000 : ℝ)|=(245485583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s0_3 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4090148083/10000000000 : ℝ)*x 0 + (616572121/2000000000 : ℝ)*x 1 + (5315412567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4090148083/10000000000 : ℝ)^4923 ≤ (4042774392393/12500000000000 : ℝ)^3899 := by
    have hnat : (4090148083 : ℕ)^4923*12500000000000^3899 ≤ 4042774392393^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4090148083 10000000000 4042774392393 12500000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (616572121/2000000000 : ℝ)^4923 ≤ (2829092339599/12500000000000 : ℝ)^3899 := by
    have hnat : (616572121 : ℕ)^4923*12500000000000^3899 ≤ 2829092339599^3899*2000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616572121 2000000000 2829092339599 12500000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5315412567/10000000000 : ℝ)^4923 ≤ (5628133265463/12500000000000 : ℝ)^3899 := by
    have hnat : (5315412567 : ℕ)^4923*12500000000000^3899 ≤ 5628133265463^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5315412567 10000000000 5628133265463 12500000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4090148083/10000000000 : ℝ), (616572121/2000000000 : ℝ), (5315412567/10000000000 : ℝ)] ![(4042774392393/12500000000000 : ℝ), (2829092339599/12500000000000 : ℝ), (5628133265463/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4090148083/10000000000 : ℝ)|^4923 ≤ (4042774392393/12500000000000 : ℝ)^3899
        have hw : |(4090148083/10000000000 : ℝ)|=(4090148083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(616572121/2000000000 : ℝ)|^4923 ≤ (2829092339599/12500000000000 : ℝ)^3899
        have hw : |(616572121/2000000000 : ℝ)|=(616572121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5315412567/10000000000 : ℝ)|^4923 ≤ (5628133265463/12500000000000 : ℝ)^3899
        have hw : |(5315412567/10000000000 : ℝ)|=(5315412567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s0_4 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-746594073/5000000000 : ℝ)*x 0 + (1235901781/2500000000 : ℝ)*x 1 + (2880977149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (746594073/5000000000 : ℝ)^4923 ≤ (9061728392631/100000000000000 : ℝ)^3899 := by
    have hnat : (746594073 : ℕ)^4923*100000000000000^3899 ≤ 9061728392631^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746594073 5000000000 9061728392631 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1235901781/2500000000 : ℝ)^4923 ≤ (41085660206217/100000000000000 : ℝ)^3899 := by
    have hnat : (1235901781 : ℕ)^4923*100000000000000^3899 ≤ 41085660206217^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235901781 2500000000 41085660206217 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2880977149/5000000000 : ℝ)^4923 ≤ (49852611390487/100000000000000 : ℝ)^3899 := by
    have hnat : (2880977149 : ℕ)^4923*100000000000000^3899 ≤ 49852611390487^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2880977149 5000000000 49852611390487 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-746594073/5000000000 : ℝ), (1235901781/2500000000 : ℝ), (2880977149/5000000000 : ℝ)] ![(9061728392631/100000000000000 : ℝ), (41085660206217/100000000000000 : ℝ), (49852611390487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-746594073/5000000000 : ℝ)|^4923 ≤ (9061728392631/100000000000000 : ℝ)^3899
        have hw : |(-746594073/5000000000 : ℝ)|=(746594073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1235901781/2500000000 : ℝ)|^4923 ≤ (41085660206217/100000000000000 : ℝ)^3899
        have hw : |(1235901781/2500000000 : ℝ)|=(1235901781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2880977149/5000000000 : ℝ)|^4923 ≤ (49852611390487/100000000000000 : ℝ)^3899
        have hw : |(2880977149/5000000000 : ℝ)|=(2880977149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s0_5 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5201975809/10000000000 : ℝ)*x 0 + (-1124170803/10000000000 : ℝ)*x 1 + (5761954297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5201975809/10000000000 : ℝ)^4923 ≤ (1752609646591/4000000000000 : ℝ)^3899 := by
    have hnat : (5201975809 : ℕ)^4923*4000000000000^3899 ≤ 1752609646591^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201975809 10000000000 1752609646591 4000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124170803/10000000000 : ℝ)^4923 ≤ (3166073718713/50000000000000 : ℝ)^3899 := by
    have hnat : (1124170803 : ℕ)^4923*50000000000000^3899 ≤ 3166073718713^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124170803 10000000000 3166073718713 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5761954297/10000000000 : ℝ)^4923 ≤ (49852611379563/100000000000000 : ℝ)^3899 := by
    have hnat : (5761954297 : ℕ)^4923*100000000000000^3899 ≤ 49852611379563^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5761954297 10000000000 49852611379563 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5201975809/10000000000 : ℝ), (-1124170803/10000000000 : ℝ), (5761954297/10000000000 : ℝ)] ![(1752609646591/4000000000000 : ℝ), (3166073718713/50000000000000 : ℝ), (49852611379563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5201975809/10000000000 : ℝ)|^4923 ≤ (1752609646591/4000000000000 : ℝ)^3899
        have hw : |(5201975809/10000000000 : ℝ)|=(5201975809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1124170803/10000000000 : ℝ)|^4923 ≤ (3166073718713/50000000000000 : ℝ)^3899
        have hw : |(-1124170803/10000000000 : ℝ)|=(1124170803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5761954297/10000000000 : ℝ)|^4923 ≤ (49852611379563/100000000000000 : ℝ)^3899
        have hw : |(5761954297/10000000000 : ℝ)|=(5761954297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s0_6 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5201975159/10000000000 : ℝ)*x 0 + (230478211/400000000 : ℝ)*x 1 + (-1124170273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5201975159/10000000000 : ℝ)^4923 ≤ (43815234252089/100000000000000 : ℝ)^3899 := by
    have hnat : (5201975159 : ℕ)^4923*100000000000000^3899 ≤ 43815234252089^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201975159 10000000000 43815234252089 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (230478211/400000000 : ℝ)^4923 ≤ (9970524412711/20000000000000 : ℝ)^3899 := by
    have hnat : (230478211 : ℕ)^4923*20000000000000^3899 ≤ 9970524412711^3899*400000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230478211 400000000 9970524412711 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124170273/10000000000 : ℝ)^4923 ≤ (1266428733607/20000000000000 : ℝ)^3899 := by
    have hnat : (1124170273 : ℕ)^4923*20000000000000^3899 ≤ 1266428733607^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124170273 10000000000 1266428733607 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5201975159/10000000000 : ℝ), (230478211/400000000 : ℝ), (-1124170273/10000000000 : ℝ)] ![(43815234252089/100000000000000 : ℝ), (9970524412711/20000000000000 : ℝ), (1266428733607/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5201975159/10000000000 : ℝ)|^4923 ≤ (43815234252089/100000000000000 : ℝ)^3899
        have hw : |(5201975159/10000000000 : ℝ)|=(5201975159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(230478211/400000000 : ℝ)|^4923 ≤ (9970524412711/20000000000000 : ℝ)^3899
        have hw : |(230478211/400000000 : ℝ)|=(230478211/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1124170273/10000000000 : ℝ)|^4923 ≤ (1266428733607/20000000000000 : ℝ)^3899
        have hw : |(-1124170273/10000000000 : ℝ)|=(1124170273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s0_7 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32000523/78125000 : ℝ)*x 0 + (657507587/1250000000 : ℝ)*x 1 + (628024649/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32000523/78125000 : ℝ)^4923 ≤ (32401300611643/100000000000000 : ℝ)^3899 := by
    have hnat : (32000523 : ℕ)^4923*100000000000000^3899 ≤ 32401300611643^3899*78125000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32000523 78125000 32401300611643 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657507587/1250000000 : ℝ)^4923 ≤ (11108467875593/25000000000000 : ℝ)^3899 := by
    have hnat : (657507587 : ℕ)^4923*25000000000000^3899 ≤ 11108467875593^3899*1250000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657507587 1250000000 11108467875593 25000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628024649/2000000000 : ℝ)^4923 ≤ (2895603484713/12500000000000 : ℝ)^3899 := by
    have hnat : (628024649 : ℕ)^4923*12500000000000^3899 ≤ 2895603484713^3899*2000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628024649 2000000000 2895603484713 12500000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32000523/78125000 : ℝ), (657507587/1250000000 : ℝ), (628024649/2000000000 : ℝ)] ![(32401300611643/100000000000000 : ℝ), (11108467875593/25000000000000 : ℝ), (2895603484713/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32000523/78125000 : ℝ)|^4923 ≤ (32401300611643/100000000000000 : ℝ)^3899
        have hw : |(32000523/78125000 : ℝ)|=(32000523/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657507587/1250000000 : ℝ)|^4923 ≤ (11108467875593/25000000000000 : ℝ)^3899
        have hw : |(657507587/1250000000 : ℝ)|=(657507587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628024649/2000000000 : ℝ)|^4923 ≤ (2895603484713/12500000000000 : ℝ)^3899
        have hw : |(628024649/2000000000 : ℝ)|=(628024649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1651_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4863/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2917/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4919/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4919 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4919*1^1024 ≤ 0^1024*1^4919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4919/1024 : ℝ) ≤ (612888160899624141/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4919 ≤ (612888160899624141/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4919*50000000000000000000^1024 ≤ 612888160899624141^1024*5^4919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 612888160899624141 50000000000000000000 4919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (612888160899624141/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4919 := by
      have hnat : (1 : ℕ)^1024*1^4919 ≤ 1^4919*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50612888160899624141/50000000000000000000 : ℝ) ≤ (10025394342134213/10000000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (50612888160899624141/50000000000000000000 : ℝ)^1024 ≤ (10025394342134213/10000000000000000 : ℝ)^4919 := by
      have hnat : (50612888160899624141 : ℕ)^1024*10000000000000000^4919 ≤ 10025394342134213^4919*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50612888160899624141 50000000000000000000 10025394342134213 10000000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10025394342134213/10000000000000000 : ℝ)) (X := (50612888160899624141/50000000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25612888160899624141/25000000000000000000 : ℝ) ≤ (5025394342134213/5000000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (25612888160899624141/25000000000000000000 : ℝ)^1024 ≤ (5025394342134213/5000000000000000 : ℝ)^4919 := by
      have hnat : (25612888160899624141 : ℕ)^1024*5000000000000000^4919 ≤ 5025394342134213^4919*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25612888160899624141 25000000000000000000 5025394342134213 5000000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5025394342134213/5000000000000000 : ℝ)) (X := (25612888160899624141/25000000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(25394342134213/4000000000000000 : ℝ)*(0 : ℝ))^(4919/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(25394342134213/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(612888160899624141/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(25394342134213/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4919/1024 : ℝ) := by
    rw [show (1 : ℝ)+(25394342134213/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10025394342134213/10000000000000000 : ℝ) by norm_num, show 1+(612888160899624141/50000000000000000000 : ℝ)+(0 : ℝ)=(50612888160899624141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(612888160899624141/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(25394342134213/4000000000000000 : ℝ)*(2/5 : ℝ))^(4919/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(25394342134213/4000000000000000 : ℝ)*(2/5 : ℝ)=(5025394342134213/5000000000000000 : ℝ) by norm_num, show 1+2*(612888160899624141/50000000000000000000 : ℝ)=(25612888160899624141/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(25394342134213/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25394342134213/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(25394342134213/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25394342134213/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(25394342134213/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25394342134213/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1490903231/10000000000 : ℝ)*X 0 0+(5784058627/10000000000 : ℝ)*X 0 1+(2461119911/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5437140329/10000000000 : ℝ)*X 1 0+(-1963884833/10000000000 : ℝ)*X 1 1+(4922240221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5437141003/10000000000 : ℝ)*X 2 0+(2461119831/5000000000 : ℝ)*X 2 1+(-245485583/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4090148083/10000000000 : ℝ)*X 0 0+(616572121/2000000000 : ℝ)*X 0 1+(5315412567/10000000000 : ℝ)*X 0 2+(4090148083/10000000000 : ℝ)*X 1 0+(616572121/2000000000 : ℝ)*X 1 1+(5315412567/10000000000 : ℝ)*X 1 2+(4090148083/10000000000 : ℝ)*X 2 0+(616572121/2000000000 : ℝ)*X 2 1+(5315412567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-746594073/5000000000 : ℝ)*X 0 0+(1235901781/2500000000 : ℝ)*X 0 1+(2880977149/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5201975809/10000000000 : ℝ)*X 1 0+(-1124170803/10000000000 : ℝ)*X 1 1+(5761954297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5201975159/10000000000 : ℝ)*X 2 0+(230478211/400000000 : ℝ)*X 2 1+(-1124170273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((32000523/78125000 : ℝ)*X 0 0+(657507587/1250000000 : ℝ)*X 0 1+(628024649/2000000000 : ℝ)*X 0 2+(32000523/78125000 : ℝ)*X 1 0+(657507587/1250000000 : ℝ)*X 1 1+(628024649/2000000000 : ℝ)*X 1 2+(32000523/78125000 : ℝ)*X 2 0+(657507587/1250000000 : ℝ)*X 2 1+(628024649/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (813015461680716337460739/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71601539/50000000000000 : ℝ)*(base1) + (1577964497/100000000000000 : ℝ)*(base19) + (1721803829/100000000000000 : ℝ)*(base23) + (162783827/100000000000000 : ℝ)*(upper3) + (64043027/25000000000000 : ℝ)*(upper5) + (402068360902099/50000000000000 : ℝ)*(major0) + (402068360902099/50000000000000 : ℝ)*(major1) + (402068360902099/50000000000000 : ℝ)*(major2) + (145042833908317/12500000000000 : ℝ)*(sp0) + (7252176658913/625000000000 : ℝ)*(sp1) + (290087030396687/25000000000000 : ℝ)*(sp2) + (447920582338483/100000000000000 : ℝ)*(sp3) + (91441589/1250000000000 : ℝ)*(sp4) + (1301835547/50000000000000 : ℝ)*(sp7) + (89584665842531/20000000000000 : ℝ)*(f.failure) + (580174921695289/50000000000000 : ℝ)*(f.sum) + (68594137486913/100000000000000000000000000000 : ℝ)*base66 + (1278147093213087/200000000000000000000000000000 : ℝ)*base67 + (353565237186913/200000000000000000000000000000 : ℝ)*base70 + (727910582413087/200000000000000000000000000000 : ℝ)*base71 + (323221711513087/100000000000000000000000000000 : ℝ)*base73 + (517793697213087/200000000000000000000000000000 : ℝ)*base75 + (520740997613087/200000000000000000000000000000 : ℝ)*base77 + (880229048413087/200000000000000000000000000000 : ℝ)*base79 + (233260710486913/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2171079/250000000000000000000 : ℝ)*base90 + (2171079/250000000000000000000 : ℝ)*base92 + (2171079/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2767757827968563986263/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2872997/160000000000 : ℝ)*(base19) + (1704356717/100000000000000 : ℝ)*(base23) + (8374099/4000000000000 : ℝ)*(base32) + (314948391/100000000000000 : ℝ)*(upper3) + (40052439/25000000000000 : ℝ)*(upper5) + (2117107306367/250000000000 : ℝ)*(major0) + (2117107306367/250000000000 : ℝ)*(major1) + (2117107306367/250000000000 : ℝ)*(major2) + (663801393/12500000000000 : ℝ)*(sp1) + (1667266447/25000000000000 : ℝ)*(sp2) + (38186680458611/3125000000000 : ℝ)*(sp4) + (610983334320641/50000000000000 : ℝ)*(sp5) + (1221965401253047/100000000000000 : ℝ)*(sp6) + (235855746015593/50000000000000 : ℝ)*(sp7) + (23585585069183/5000000000000 : ℝ)*(f.failure) + (38186680458611/3125000000000 : ℝ)*(f.sum) + (123768938171/500000000000000000000000000 : ℝ)*base65 + (8642274469829/1000000000000000000000000000 : ℝ)*base68 + (127017631829/1000000000000000000000000000 : ℝ)*base70 + (2830534336171/1000000000000000000000000000 : ℝ)*base71 + (4843675094829/500000000000000000000000000 : ℝ)*base74 + (7259993286171/1000000000000000000000000000 : ℝ)*base75 + (299656986829/1000000000000000000000000000 : ℝ)*base78 + (4938798602829/1000000000000000000000000000 : ℝ)*base80 + (689162319329/500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (674547/62500000000000000000 : ℝ)*base90 + (674547/62500000000000000000 : ℝ)*base92 + (674547/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1651_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4863/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2917/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1651_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1651_s1_0 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1596368843/10000000000 : ℝ)*x 0 + (1373882009/2500000000 : ℝ)*x 1 + (1028442537/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1596368843/10000000000 : ℝ)^4923 ≤ (9859411109101/100000000000000 : ℝ)^3899 := by
    have hnat : (1596368843 : ℕ)^4923*100000000000000^3899 ≤ 9859411109101^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596368843 10000000000 9859411109101 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373882009/2500000000 : ℝ)^4923 ≤ (46959961092447/100000000000000 : ℝ)^3899 := by
    have hnat : (1373882009 : ℕ)^4923*100000000000000^3899 ≤ 46959961092447^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373882009 2500000000 46959961092447 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028442537/2000000000 : ℝ)^4923 ≤ (43180627783793/100000000000000 : ℝ)^3899 := by
    have hnat : (1028442537 : ℕ)^4923*100000000000000^3899 ≤ 43180627783793^3899*2000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028442537 2000000000 43180627783793 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1596368843/10000000000 : ℝ), (1373882009/2500000000 : ℝ), (1028442537/2000000000 : ℝ)] ![(9859411109101/100000000000000 : ℝ), (46959961092447/100000000000000 : ℝ), (43180627783793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1596368843/10000000000 : ℝ)|^4923 ≤ (9859411109101/100000000000000 : ℝ)^3899
        have hw : |(-1596368843/10000000000 : ℝ)|=(1596368843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1373882009/2500000000 : ℝ)|^4923 ≤ (46959961092447/100000000000000 : ℝ)^3899
        have hw : |(1373882009/2500000000 : ℝ)|=(1373882009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1028442537/2000000000 : ℝ)|^4923 ≤ (43180627783793/100000000000000 : ℝ)^3899
        have hw : |(1028442537/2000000000 : ℝ)|=(1028442537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s1_1 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2680197963/5000000000 : ℝ)*x 0 + (-890013143/5000000000 : ℝ)*x 1 + (642776569/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680197963/5000000000 : ℝ)^4923 ≤ (45506711313913/100000000000000 : ℝ)^3899 := by
    have hnat : (2680197963 : ℕ)^4923*100000000000000^3899 ≤ 45506711313913^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680197963 5000000000 45506711313913 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (890013143/5000000000 : ℝ)^4923 ≤ (2828165574263/25000000000000 : ℝ)^3899 := by
    have hnat : (890013143 : ℕ)^4923*25000000000000^3899 ≤ 2828165574263^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890013143 5000000000 2828165574263 25000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642776569/1250000000 : ℝ)^4923 ≤ (43180626373637/100000000000000 : ℝ)^3899 := by
    have hnat : (642776569 : ℕ)^4923*100000000000000^3899 ≤ 43180626373637^3899*1250000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642776569 1250000000 43180626373637 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680197963/5000000000 : ℝ), (-890013143/5000000000 : ℝ), (642776569/1250000000 : ℝ)] ![(45506711313913/100000000000000 : ℝ), (2828165574263/25000000000000 : ℝ), (43180626373637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680197963/5000000000 : ℝ)|^4923 ≤ (45506711313913/100000000000000 : ℝ)^3899
        have hw : |(2680197963/5000000000 : ℝ)|=(2680197963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-890013143/5000000000 : ℝ)|^4923 ≤ (2828165574263/25000000000000 : ℝ)^3899
        have hw : |(-890013143/5000000000 : ℝ)|=(890013143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642776569/1250000000 : ℝ)|^4923 ≤ (43180626373637/100000000000000 : ℝ)^3899
        have hw : |(642776569/1250000000 : ℝ)|=(642776569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s1_2 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072079077/2000000000 : ℝ)*x 0 + (1028442629/2000000000 : ℝ)*x 1 + (-890013113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072079077/2000000000 : ℝ)^4923 ≤ (22753352757461/50000000000000 : ℝ)^3899 := by
    have hnat : (1072079077 : ℕ)^4923*50000000000000^3899 ≤ 22753352757461^3899*2000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072079077 2000000000 22753352757461 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028442629/2000000000 : ℝ)^4923 ≤ (1349394770657/3125000000000 : ℝ)^3899 := by
    have hnat : (1028442629 : ℕ)^4923*3125000000000^3899 ≤ 1349394770657^3899*2000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028442629 2000000000 1349394770657 3125000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (890013113/5000000000 : ℝ)^4923 ≤ (2262532363117/20000000000000 : ℝ)^3899 := by
    have hnat : (890013113 : ℕ)^4923*20000000000000^3899 ≤ 2262532363117^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890013113 5000000000 2262532363117 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072079077/2000000000 : ℝ), (1028442629/2000000000 : ℝ), (-890013113/5000000000 : ℝ)] ![(22753352757461/50000000000000 : ℝ), (1349394770657/3125000000000 : ℝ), (2262532363117/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072079077/2000000000 : ℝ)|^4923 ≤ (22753352757461/50000000000000 : ℝ)^3899
        have hw : |(1072079077/2000000000 : ℝ)|=(1072079077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028442629/2000000000 : ℝ)|^4923 ≤ (1349394770657/3125000000000 : ℝ)^3899
        have hw : |(1028442629/2000000000 : ℝ)|=(1028442629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-890013113/5000000000 : ℝ)|^4923 ≤ (2262532363117/20000000000000 : ℝ)^3899
        have hw : |(-890013113/5000000000 : ℝ)|=(890013113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s1_3 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4172634363/10000000000 : ℝ)*x 0 + (3733134899/10000000000 : ℝ)*x 1 + (2324201029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4172634363/10000000000 : ℝ)^4923 ≤ (33167913124967/100000000000000 : ℝ)^3899 := by
    have hnat : (4172634363 : ℕ)^4923*100000000000000^3899 ≤ 33167913124967^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172634363 10000000000 33167913124967 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3733134899/10000000000 : ℝ)^4923 ≤ (28819522265109/100000000000000 : ℝ)^3899 := by
    have hnat : (3733134899 : ℕ)^4923*100000000000000^3899 ≤ 28819522265109^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3733134899 10000000000 28819522265109 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2324201029/5000000000 : ℝ)^4923 ≤ (19006282296409/50000000000000 : ℝ)^3899 := by
    have hnat : (2324201029 : ℕ)^4923*50000000000000^3899 ≤ 19006282296409^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2324201029 5000000000 19006282296409 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4172634363/10000000000 : ℝ), (3733134899/10000000000 : ℝ), (2324201029/5000000000 : ℝ)] ![(33167913124967/100000000000000 : ℝ), (28819522265109/100000000000000 : ℝ), (19006282296409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4172634363/10000000000 : ℝ)|^4923 ≤ (33167913124967/100000000000000 : ℝ)^3899
        have hw : |(4172634363/10000000000 : ℝ)|=(4172634363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3733134899/10000000000 : ℝ)|^4923 ≤ (28819522265109/100000000000000 : ℝ)^3899
        have hw : |(3733134899/10000000000 : ℝ)|=(3733134899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2324201029/5000000000 : ℝ)|^4923 ≤ (19006282296409/50000000000000 : ℝ)^3899
        have hw : |(2324201029/5000000000 : ℝ)|=(2324201029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s1_4 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1596523473/10000000000 : ℝ)*x 0 + (2572896193/5000000000 : ℝ)*x 1 + (5491897867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1596523473/10000000000 : ℝ)^4923 ≤ (1972123392001/20000000000000 : ℝ)^3899 := by
    have hnat : (1596523473 : ℕ)^4923*20000000000000^3899 ≤ 1972123392001^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596523473 10000000000 1972123392001 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2572896193/5000000000 : ℝ)^4923 ≤ (2701161604063/6250000000000 : ℝ)^3899 := by
    have hnat : (2572896193 : ℕ)^4923*6250000000000^3899 ≤ 2701161604063^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2572896193 5000000000 2701161604063 6250000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5491897867/10000000000 : ℝ)^4923 ≤ (11730199340219/25000000000000 : ℝ)^3899 := by
    have hnat : (5491897867 : ℕ)^4923*25000000000000^3899 ≤ 11730199340219^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491897867 10000000000 11730199340219 25000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1596523473/10000000000 : ℝ), (2572896193/5000000000 : ℝ), (5491897867/10000000000 : ℝ)] ![(1972123392001/20000000000000 : ℝ), (2701161604063/6250000000000 : ℝ), (11730199340219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1596523473/10000000000 : ℝ)|^4923 ≤ (1972123392001/20000000000000 : ℝ)^3899
        have hw : |(-1596523473/10000000000 : ℝ)|=(1596523473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2572896193/5000000000 : ℝ)|^4923 ≤ (2701161604063/6250000000000 : ℝ)^3899
        have hw : |(2572896193/5000000000 : ℝ)|=(2572896193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5491897867/10000000000 : ℝ)|^4923 ≤ (11730199340219/25000000000000 : ℝ)^3899
        have hw : |(5491897867/10000000000 : ℝ)|=(5491897867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s1_5 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632958911/5000000000 : ℝ)*x 0 + (-1430341123/10000000000 : ℝ)*x 1 + (5491897893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632958911/5000000000 : ℝ)^4923 ≤ (22248176256649/50000000000000 : ℝ)^3899 := by
    have hnat : (2632958911 : ℕ)^4923*50000000000000^3899 ≤ 22248176256649^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632958911 5000000000 22248176256649 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1430341123/10000000000 : ℝ)^4923 ≤ (8582849834897/100000000000000 : ℝ)^3899 := by
    have hnat : (1430341123 : ℕ)^4923*100000000000000^3899 ≤ 8582849834897^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1430341123 10000000000 8582849834897 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5491897893/10000000000 : ℝ)^4923 ≤ (938415952827/2000000000000 : ℝ)^3899 := by
    have hnat : (5491897893 : ℕ)^4923*2000000000000^3899 ≤ 938415952827^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491897893 10000000000 938415952827 2000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632958911/5000000000 : ℝ), (-1430341123/10000000000 : ℝ), (5491897893/10000000000 : ℝ)] ![(22248176256649/50000000000000 : ℝ), (8582849834897/100000000000000 : ℝ), (938415952827/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632958911/5000000000 : ℝ)|^4923 ≤ (22248176256649/50000000000000 : ℝ)^3899
        have hw : |(2632958911/5000000000 : ℝ)|=(2632958911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1430341123/10000000000 : ℝ)|^4923 ≤ (8582849834897/100000000000000 : ℝ)^3899
        have hw : |(-1430341123/10000000000 : ℝ)|=(1430341123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5491897893/10000000000 : ℝ)|^4923 ≤ (938415952827/2000000000000 : ℝ)^3899
        have hw : |(5491897893/10000000000 : ℝ)|=(5491897893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s1_6 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329119851/625000000 : ℝ)*x 0 + (5491898181/10000000000 : ℝ)*x 1 + (-1430341003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329119851/625000000 : ℝ)^4923 ≤ (44496350315467/100000000000000 : ℝ)^3899 := by
    have hnat : (329119851 : ℕ)^4923*100000000000000^3899 ≤ 44496350315467^3899*625000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329119851 625000000 44496350315467 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5491898181/10000000000 : ℝ)^4923 ≤ (46920800748141/100000000000000 : ℝ)^3899 := by
    have hnat : (5491898181 : ℕ)^4923*100000000000000^3899 ≤ 46920800748141^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491898181 10000000000 46920800748141 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1430341003/10000000000 : ℝ)^4923 ≤ (4291424462859/50000000000000 : ℝ)^3899 := by
    have hnat : (1430341003 : ℕ)^4923*50000000000000^3899 ≤ 4291424462859^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1430341003 10000000000 4291424462859 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329119851/625000000 : ℝ), (5491898181/10000000000 : ℝ), (-1430341003/10000000000 : ℝ)] ![(44496350315467/100000000000000 : ℝ), (46920800748141/100000000000000 : ℝ), (4291424462859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329119851/625000000 : ℝ)|^4923 ≤ (44496350315467/100000000000000 : ℝ)^3899
        have hw : |(329119851/625000000 : ℝ)|=(329119851/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5491898181/10000000000 : ℝ)|^4923 ≤ (46920800748141/100000000000000 : ℝ)^3899
        have hw : |(5491898181/10000000000 : ℝ)|=(5491898181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1430341003/10000000000 : ℝ)|^4923 ≤ (4291424462859/50000000000000 : ℝ)^3899
        have hw : |(-1430341003/10000000000 : ℝ)|=(1430341003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s1_7 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1043258791/2500000000 : ℝ)*x 0 + (1159782287/2500000000 : ℝ)*x 1 + (3742539121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043258791/2500000000 : ℝ)^4923 ≤ (16585967917329/50000000000000 : ℝ)^3899 := by
    have hnat : (1043258791 : ℕ)^4923*50000000000000^3899 ≤ 16585967917329^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043258791 2500000000 16585967917329 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1159782287/2500000000 : ℝ)^4923 ≤ (758336893599/2000000000000 : ℝ)^3899 := by
    have hnat : (1159782287 : ℕ)^4923*2000000000000^3899 ≤ 758336893599^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159782287 2500000000 758336893599 2000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3742539121/10000000000 : ℝ)^4923 ≤ (28911219474513/100000000000000 : ℝ)^3899 := by
    have hnat : (3742539121 : ℕ)^4923*100000000000000^3899 ≤ 28911219474513^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3742539121 10000000000 28911219474513 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1043258791/2500000000 : ℝ), (1159782287/2500000000 : ℝ), (3742539121/10000000000 : ℝ)] ![(16585967917329/50000000000000 : ℝ), (758336893599/2000000000000 : ℝ), (28911219474513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1043258791/2500000000 : ℝ)|^4923 ≤ (16585967917329/50000000000000 : ℝ)^3899
        have hw : |(1043258791/2500000000 : ℝ)|=(1043258791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1159782287/2500000000 : ℝ)|^4923 ≤ (758336893599/2000000000000 : ℝ)^3899
        have hw : |(1159782287/2500000000 : ℝ)|=(1159782287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3742539121/10000000000 : ℝ)|^4923 ≤ (28911219474513/100000000000000 : ℝ)^3899
        have hw : |(3742539121/10000000000 : ℝ)|=(3742539121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1651_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2917/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4863/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9771/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8639/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2917/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4863/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2917/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4863/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2917/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4863/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2917/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4863/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2917/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4863/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2917/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4863/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4863/100000 : ℝ) ^ (4919/1024 : ℝ) ≤ (24617144905469/50000000000000000000 : ℝ) := by
    have hpowers : (4863/100000 : ℝ)^4919 ≤ (24617144905469/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4863 : ℕ)^4919*50000000000000000000^1024 ≤ 24617144905469^1024*100000^4919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4863 100000 24617144905469 50000000000000000000 4919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4863/100000 : ℝ)) (X := (24617144905469/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2917/12500 : ℝ) ^ (4919/1024 : ℝ) ≤ (4604172507036047/5000000000000000000 : ℝ) := by
    have hpowers : (2917/12500 : ℝ)^4919 ≤ (4604172507036047/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2917 : ℕ)^4919*5000000000000000000^1024 ≤ 4604172507036047^1024*12500^4919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2917 12500 4604172507036047 5000000000000000000 4919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2917/12500 : ℝ)) (X := (4604172507036047/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000024617144905469/25000000000000000000 : ℝ) ≤ (2000000409968637/2000000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (25000024617144905469/25000000000000000000 : ℝ)^1024 ≤ (2000000409968637/2000000000000000 : ℝ)^4919 := by
      have hnat : (25000024617144905469 : ℕ)^1024*2000000000000000^4919 ≤ 2000000409968637^4919*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000024617144905469 25000000000000000000 2000000409968637 2000000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000409968637/2000000000000000 : ℝ)) (X := (25000024617144905469/25000000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50046066342215265939/50000000000000000000 : ℝ) ≤ (10001917248919391/10000000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (50046066342215265939/50000000000000000000 : ℝ)^1024 ≤ (10001917248919391/10000000000000000 : ℝ)^4919 := by
      have hnat : (50046066342215265939 : ℕ)^1024*10000000000000000^4919 ≤ 10001917248919391^4919*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50046066342215265939 50000000000000000000 10001917248919391 10000000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001917248919391/10000000000000000 : ℝ)) (X := (50046066342215265939/50000000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2504604172507036047/2500000000000000000 : ℝ) ≤ (10003832447995597/10000000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (2504604172507036047/2500000000000000000 : ℝ)^1024 ≤ (10003832447995597/10000000000000000 : ℝ)^4919 := by
      have hnat : (2504604172507036047 : ℕ)^1024*10000000000000000^4919 ≤ 10003832447995597^4919*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2504604172507036047 2500000000000000000 10003832447995597 10000000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003832447995597/10000000000000000 : ℝ)) (X := (2504604172507036047/2500000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(24617144905469/50000000000000000000 : ℝ) ≤ ((14208570049272152073/14210000000000000000 : ℝ)+2*(73661502931/71050000000000 : ℝ)*(4863/100000 : ℝ))^(4919/1024 : ℝ) := by
    rw [show (14208570049272152073/14210000000000000000 : ℝ)+2*(73661502931/71050000000000 : ℝ)*(4863/100000 : ℝ)=(2000000409968637/2000000000000000 : ℝ) by norm_num, show 1+2*(24617144905469/50000000000000000000 : ℝ)=(25000024617144905469/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4604172507036047/5000000000000000000 : ℝ)+(24617144905469/50000000000000000000 : ℝ) ≤ ((14208570049272152073/14210000000000000000 : ℝ)+(73661502931/71050000000000 : ℝ)*((2917/12500 : ℝ)+(4863/100000 : ℝ)))^(4919/1024 : ℝ) := by
    rw [show (14208570049272152073/14210000000000000000 : ℝ)+(73661502931/71050000000000 : ℝ)*((2917/12500 : ℝ)+(4863/100000 : ℝ))=(10001917248919391/10000000000000000 : ℝ) by norm_num, show 1+(4604172507036047/5000000000000000000 : ℝ)+(24617144905469/50000000000000000000 : ℝ)=(50046066342215265939/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4604172507036047/5000000000000000000 : ℝ) ≤ ((14208570049272152073/14210000000000000000 : ℝ)+2*(73661502931/71050000000000 : ℝ)*(2917/12500 : ℝ))^(4919/1024 : ℝ) := by
    rw [show (14208570049272152073/14210000000000000000 : ℝ)+2*(73661502931/71050000000000 : ℝ)*(2917/12500 : ℝ)=(10003832447995597/10000000000000000 : ℝ) by norm_num, show 1+2*(4604172507036047/5000000000000000000 : ℝ)=(2504604172507036047/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14208570049272152073/14210000000000000000 : ℝ)*(X 1 0+X 2 0)+(73661502931/71050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (4863/100000 : ℝ)) (hi := (2917/12500 : ℝ)) (c := (14208570049272152073/14210000000000000000 : ℝ)) (alpha := (73661502931/71050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14208570049272152073/14210000000000000000 : ℝ)*(X 0 1+X 2 1)+(73661502931/71050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (4863/100000 : ℝ)) (hi := (2917/12500 : ℝ)) (c := (14208570049272152073/14210000000000000000 : ℝ)) (alpha := (73661502931/71050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14208570049272152073/14210000000000000000 : ℝ)*(X 0 2+X 1 2)+(73661502931/71050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (4863/100000 : ℝ)) (hi := (2917/12500 : ℝ)) (c := (14208570049272152073/14210000000000000000 : ℝ)) (alpha := (73661502931/71050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1596368843/10000000000 : ℝ)*X 0 0+(1373882009/2500000000 : ℝ)*X 0 1+(1028442537/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2680197963/5000000000 : ℝ)*X 1 0+(-890013143/5000000000 : ℝ)*X 1 1+(642776569/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1072079077/2000000000 : ℝ)*X 2 0+(1028442629/2000000000 : ℝ)*X 2 1+(-890013113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4172634363/10000000000 : ℝ)*X 0 0+(3733134899/10000000000 : ℝ)*X 0 1+(2324201029/5000000000 : ℝ)*X 0 2+(4172634363/10000000000 : ℝ)*X 1 0+(3733134899/10000000000 : ℝ)*X 1 1+(2324201029/5000000000 : ℝ)*X 1 2+(4172634363/10000000000 : ℝ)*X 2 0+(3733134899/10000000000 : ℝ)*X 2 1+(2324201029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1596523473/10000000000 : ℝ)*X 0 0+(2572896193/5000000000 : ℝ)*X 0 1+(5491897867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2632958911/5000000000 : ℝ)*X 1 0+(-1430341123/10000000000 : ℝ)*X 1 1+(5491897893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((329119851/625000000 : ℝ)*X 2 0+(5491898181/10000000000 : ℝ)*X 2 1+(-1430341003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1043258791/2500000000 : ℝ)*X 0 0+(1159782287/2500000000 : ℝ)*X 0 1+(3742539121/10000000000 : ℝ)*X 0 2+(1043258791/2500000000 : ℝ)*X 1 0+(1159782287/2500000000 : ℝ)*X 1 1+(3742539121/10000000000 : ℝ)*X 1 2+(1043258791/2500000000 : ℝ)*X 2 0+(1159782287/2500000000 : ℝ)*X 2 1+(3742539121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21336026101633201397517/3552500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1565161441/100000000000000 : ℝ)*(base19) + (1173941163/100000000000000 : ℝ)*(base23) + (29450717/12500000000000 : ℝ)*(upper3) + (56587041/100000000000000 : ℝ)*(upper4) + (155180733/100000000000000 : ℝ)*(upper5) + (1961475342122661/100000000000000 : ℝ)*(major0) + (1961475342122661/100000000000000 : ℝ)*(major1) + (1961475342122661/100000000000000 : ℝ)*(major2) + (88448375529069/3125000000000 : ℝ)*(sp0) + (1415180190328913/50000000000000 : ℝ)*(sp1) + (566072154375621/20000000000000 : ℝ)*(sp2) + (1092582640948343/100000000000000 : ℝ)*(sp3) + (13928889059/100000000000000 : ℝ)*(sp4) + (184290013/3125000000000 : ℝ)*(sp7) + (1092588538228759/100000000000000 : ℝ)*(f.failure) + (707590486454817/25000000000000 : ℝ)*(f.sum) + (3784405269793/1776250000000000000000000000 : ℝ)*base65 + (3722587190437373747/1421000000000000000000000000000000 : ℝ)*base68 + (3585096183966626253/1421000000000000000000000000000000 : ℝ)*base69 + (1106864018900626253/1421000000000000000000000000000000 : ℝ)*base71 + (2411062521563/7105000000000000000000000000 : ℝ)*base74 + (6803368004667626253/1421000000000000000000000000000000 : ℝ)*base75 + (1925732649228373747/1421000000000000000000000000000000 : ℝ)*base78 + (20644528691860373747/1421000000000000000000000000000000 : ℝ)*base80 + (14312538988141/3552500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (5532469/1250000000000000000000 : ℝ)*base89 + (5532469/1250000000000000000000 : ℝ)*base91 + (5532469/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1881961125132326785972231257/355250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (541185137/50000000000000 : ℝ)*(base19) + (533047467/50000000000000 : ℝ)*(base23) + (1826329/5000000000000 : ℝ)*(upper2) + (69904117/50000000000000 : ℝ)*(upper3) + (32646779/25000000000000 : ℝ)*(upper5) + (1001157169825403/50000000000000 : ℝ)*(major0) + (1001157169825403/50000000000000 : ℝ)*(major1) + (1001157169825403/50000000000000 : ℝ)*(major2) + (2542625139/25000000000000 : ℝ)*(sp1) + (731066871/6250000000000 : ℝ)*(sp2) + (722322917257843/25000000000000 : ℝ)*(sp4) + (2889280416160541/100000000000000 : ℝ)*(sp5) + (1444639452933251/50000000000000 : ℝ)*(sp6) + (557668416842313/50000000000000 : ℝ)*(sp7) + (557668416842313/50000000000000 : ℝ)*(f.failure) + (722322917257843/25000000000000 : ℝ)*(f.sum) + (2729566033821/888125000000000000000000000 : ℝ)*base66 + (2634618198193110419/710500000000000000000000000000000 : ℝ)*base67 + (4845614635621889581/710500000000000000000000000000000 : ℝ)*base70 + (3619390394482110419/710500000000000000000000000000000 : ℝ)*base71 + (9640386387573/7105000000000000000000000000 : ℝ)*base74 + (1727184309082389581/710500000000000000000000000000000 : ℝ)*base76 + (753415983674889581/710500000000000000000000000000000 : ℝ)*base78 + (4053608178701889581/710500000000000000000000000000000 : ℝ)*base80 + (11636107156787/1776250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4258283/625000000000000000000 : ℝ)*base89 + (4258283/625000000000000000000 : ℝ)*base91 + (4258283/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1651_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2917/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4863/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9771/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8639/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1651_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1651_s2_0 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-802788449/5000000000 : ℝ)*x 0 + (681341571/1250000000 : ℝ)*x 1 + (2590466051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (802788449/5000000000 : ℝ)^4923 ≤ (1986254334017/20000000000000 : ℝ)^3899 := by
    have hnat : (802788449 : ℕ)^4923*20000000000000^3899 ≤ 1986254334017^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802788449 5000000000 1986254334017 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681341571/1250000000 : ℝ)^4923 ≤ (9295433181293/20000000000000 : ℝ)^3899 := by
    have hnat : (681341571 : ℕ)^4923*20000000000000^3899 ≤ 9295433181293^3899*1250000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681341571 1250000000 9295433181293 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590466051/5000000000 : ℝ)^4923 ≤ (43591562413279/100000000000000 : ℝ)^3899 := by
    have hnat : (2590466051 : ℕ)^4923*100000000000000^3899 ≤ 43591562413279^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590466051 5000000000 43591562413279 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-802788449/5000000000 : ℝ), (681341571/1250000000 : ℝ), (2590466051/5000000000 : ℝ)] ![(1986254334017/20000000000000 : ℝ), (9295433181293/20000000000000 : ℝ), (43591562413279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-802788449/5000000000 : ℝ)|^4923 ≤ (1986254334017/20000000000000 : ℝ)^3899
        have hw : |(-802788449/5000000000 : ℝ)|=(802788449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681341571/1250000000 : ℝ)|^4923 ≤ (9295433181293/20000000000000 : ℝ)^3899
        have hw : |(681341571/1250000000 : ℝ)|=(681341571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590466051/5000000000 : ℝ)|^4923 ≤ (43591562413279/100000000000000 : ℝ)^3899
        have hw : |(2590466051/5000000000 : ℝ)|=(2590466051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s2_1 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348535007/10000000000 : ℝ)*x 0 + (-436140127/2500000000 : ℝ)*x 1 + (647616623/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348535007/10000000000 : ℝ)^4923 ≤ (11344902704371/25000000000000 : ℝ)^3899 := by
    have hnat : (5348535007 : ℕ)^4923*25000000000000^3899 ≤ 11344902704371^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348535007 10000000000 11344902704371 25000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436140127/2500000000 : ℝ)^4923 ≤ (5514408695319/50000000000000 : ℝ)^3899 := by
    have hnat : (436140127 : ℕ)^4923*50000000000000^3899 ≤ 5514408695319^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436140127 2500000000 5514408695319 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647616623/1250000000 : ℝ)^4923 ≤ (21795785891641/50000000000000 : ℝ)^3899 := by
    have hnat : (647616623 : ℕ)^4923*50000000000000^3899 ≤ 21795785891641^3899*1250000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647616623 1250000000 21795785891641 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348535007/10000000000 : ℝ), (-436140127/2500000000 : ℝ), (647616623/1250000000 : ℝ)] ![(11344902704371/25000000000000 : ℝ), (5514408695319/50000000000000 : ℝ), (21795785891641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348535007/10000000000 : ℝ)|^4923 ≤ (11344902704371/25000000000000 : ℝ)^3899
        have hw : |(5348535007/10000000000 : ℝ)|=(5348535007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436140127/2500000000 : ℝ)|^4923 ≤ (5514408695319/50000000000000 : ℝ)^3899
        have hw : |(-436140127/2500000000 : ℝ)|=(436140127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647616623/1250000000 : ℝ)|^4923 ≤ (21795785891641/50000000000000 : ℝ)^3899
        have hw : |(647616623/1250000000 : ℝ)|=(647616623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s2_2 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334283519/625000000 : ℝ)*x 0 + (5180931933/10000000000 : ℝ)*x 1 + (-872280083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334283519/625000000 : ℝ)^4923 ≤ (45379624711971/100000000000000 : ℝ)^3899 := by
    have hnat : (334283519 : ℕ)^4923*100000000000000^3899 ≤ 45379624711971^3899*625000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334283519 625000000 45379624711971 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180931933/10000000000 : ℝ)^4923 ≤ (43591560617893/100000000000000 : ℝ)^3899 := by
    have hnat : (5180931933 : ℕ)^4923*100000000000000^3899 ≤ 43591560617893^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180931933 10000000000 43591560617893 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (872280083/5000000000 : ℝ)^4923 ≤ (2205762932149/20000000000000 : ℝ)^3899 := by
    have hnat : (872280083 : ℕ)^4923*20000000000000^3899 ≤ 2205762932149^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872280083 5000000000 2205762932149 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334283519/625000000 : ℝ), (5180931933/10000000000 : ℝ), (-872280083/5000000000 : ℝ)] ![(45379624711971/100000000000000 : ℝ), (43591560617893/100000000000000 : ℝ), (2205762932149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334283519/625000000 : ℝ)|^4923 ≤ (45379624711971/100000000000000 : ℝ)^3899
        have hw : |(334283519/625000000 : ℝ)|=(334283519/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180931933/10000000000 : ℝ)|^4923 ≤ (43591560617893/100000000000000 : ℝ)^3899
        have hw : |(5180931933/10000000000 : ℝ)|=(5180931933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-872280083/5000000000 : ℝ)|^4923 ≤ (2205762932149/20000000000000 : ℝ)^3899
        have hw : |(-872280083/5000000000 : ℝ)|=(872280083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s2_3 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2089750243/5000000000 : ℝ)*x 0 + (3840619639/10000000000 : ℝ)*x 1 + (4539539059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089750243/5000000000 : ℝ)^4923 ≤ (33236840190853/100000000000000 : ℝ)^3899 := by
    have hnat : (2089750243 : ℕ)^4923*100000000000000^3899 ≤ 33236840190853^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089750243 5000000000 33236840190853 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3840619639/10000000000 : ℝ)^4923 ≤ (14935577356913/50000000000000 : ℝ)^3899 := by
    have hnat : (3840619639 : ℕ)^4923*50000000000000^3899 ≤ 14935577356913^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3840619639 10000000000 14935577356913 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4539539059/10000000000 : ℝ)^4923 ≤ (36892005076681/100000000000000 : ℝ)^3899 := by
    have hnat : (4539539059 : ℕ)^4923*100000000000000^3899 ≤ 36892005076681^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539539059 10000000000 36892005076681 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089750243/5000000000 : ℝ), (3840619639/10000000000 : ℝ), (4539539059/10000000000 : ℝ)] ![(33236840190853/100000000000000 : ℝ), (14935577356913/50000000000000 : ℝ), (36892005076681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089750243/5000000000 : ℝ)|^4923 ≤ (33236840190853/100000000000000 : ℝ)^3899
        have hw : |(2089750243/5000000000 : ℝ)|=(2089750243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3840619639/10000000000 : ℝ)|^4923 ≤ (14935577356913/50000000000000 : ℝ)^3899
        have hw : |(3840619639/10000000000 : ℝ)|=(3840619639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4539539059/10000000000 : ℝ)|^4923 ≤ (36892005076681/100000000000000 : ℝ)^3899
        have hw : |(4539539059/10000000000 : ℝ)|=(4539539059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s2_4 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-802822653/5000000000 : ℝ)*x 0 + (5183025441/10000000000 : ℝ)*x 1 + (5448617111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (802822653/5000000000 : ℝ)^4923 ≤ (1986361187743/20000000000000 : ℝ)^3899 := by
    have hnat : (802822653 : ℕ)^4923*20000000000000^3899 ≤ 1986361187743^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802822653 5000000000 1986361187743 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183025441/10000000000 : ℝ)^4923 ≤ (10903450589963/25000000000000 : ℝ)^3899 := by
    have hnat : (5183025441 : ℕ)^4923*25000000000000^3899 ≤ 10903450589963^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183025441 10000000000 10903450589963 25000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448617111/10000000000 : ℝ)^4923 ≤ (2903399480673/6250000000000 : ℝ)^3899 := by
    have hnat : (5448617111 : ℕ)^4923*6250000000000^3899 ≤ 2903399480673^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448617111 10000000000 2903399480673 6250000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-802822653/5000000000 : ℝ), (5183025441/10000000000 : ℝ), (5448617111/10000000000 : ℝ)] ![(1986361187743/20000000000000 : ℝ), (10903450589963/25000000000000 : ℝ), (2903399480673/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-802822653/5000000000 : ℝ)|^4923 ≤ (1986361187743/20000000000000 : ℝ)^3899
        have hw : |(-802822653/5000000000 : ℝ)|=(802822653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183025441/10000000000 : ℝ)|^4923 ≤ (10903450589963/25000000000000 : ℝ)^3899
        have hw : |(5183025441/10000000000 : ℝ)|=(5183025441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448617111/10000000000 : ℝ)|^4923 ≤ (2903399480673/6250000000000 : ℝ)^3899
        have hw : |(5448617111/10000000000 : ℝ)|=(5448617111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s2_5 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276445037/10000000000 : ℝ)*x 0 + (-1476875431/10000000000 : ℝ)*x 1 + (5448617051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276445037/10000000000 : ℝ)^4923 ≤ (22304348836573/50000000000000 : ℝ)^3899 := by
    have hnat : (5276445037 : ℕ)^4923*50000000000000^3899 ≤ 22304348836573^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276445037 10000000000 22304348836573 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1476875431/10000000000 : ℝ)^4923 ≤ (4468455631579/50000000000000 : ℝ)^3899 := by
    have hnat : (1476875431 : ℕ)^4923*50000000000000^3899 ≤ 4468455631579^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1476875431 10000000000 4468455631579 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448617051/10000000000 : ℝ)^4923 ≤ (181462465019/390625000000 : ℝ)^3899 := by
    have hnat : (5448617051 : ℕ)^4923*390625000000^3899 ≤ 181462465019^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448617051 10000000000 181462465019 390625000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276445037/10000000000 : ℝ), (-1476875431/10000000000 : ℝ), (5448617051/10000000000 : ℝ)] ![(22304348836573/50000000000000 : ℝ), (4468455631579/50000000000000 : ℝ), (181462465019/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276445037/10000000000 : ℝ)|^4923 ≤ (22304348836573/50000000000000 : ℝ)^3899
        have hw : |(5276445037/10000000000 : ℝ)|=(5276445037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1476875431/10000000000 : ℝ)|^4923 ≤ (4468455631579/50000000000000 : ℝ)^3899
        have hw : |(-1476875431/10000000000 : ℝ)|=(1476875431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448617051/10000000000 : ℝ)|^4923 ≤ (181462465019/390625000000 : ℝ)^3899
        have hw : |(5448617051/10000000000 : ℝ)|=(5448617051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s2_6 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638222681/5000000000 : ℝ)*x 0 + (5448616633/10000000000 : ℝ)*x 1 + (-738437783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638222681/5000000000 : ℝ)^4923 ≤ (2788043821401/6250000000000 : ℝ)^3899 := by
    have hnat : (2638222681 : ℕ)^4923*6250000000000^3899 ≤ 2788043821401^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638222681 5000000000 2788043821401 6250000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5448616633/10000000000 : ℝ)^4923 ≤ (23227193272531/50000000000000 : ℝ)^3899 := by
    have hnat : (5448616633 : ℕ)^4923*50000000000000^3899 ≤ 23227193272531^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448616633 10000000000 23227193272531 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (738437783/5000000000 : ℝ)^4923 ≤ (4468456147311/50000000000000 : ℝ)^3899 := by
    have hnat : (738437783 : ℕ)^4923*50000000000000^3899 ≤ 4468456147311^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738437783 5000000000 4468456147311 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638222681/5000000000 : ℝ), (5448616633/10000000000 : ℝ), (-738437783/5000000000 : ℝ)] ![(2788043821401/6250000000000 : ℝ), (23227193272531/50000000000000 : ℝ), (4468456147311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638222681/5000000000 : ℝ)|^4923 ≤ (2788043821401/6250000000000 : ℝ)^3899
        have hw : |(2638222681/5000000000 : ℝ)|=(2638222681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5448616633/10000000000 : ℝ)|^4923 ≤ (23227193272531/50000000000000 : ℝ)^3899
        have hw : |(5448616633/10000000000 : ℝ)|=(5448616633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-738437783/5000000000 : ℝ)|^4923 ≤ (4468456147311/50000000000000 : ℝ)^3899
        have hw : |(-738437783/5000000000 : ℝ)|=(738437783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s2_7 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2089839767/5000000000 : ℝ)*x 0 + (2267058757/5000000000 : ℝ)*x 1 + (3846099563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089839767/5000000000 : ℝ)^4923 ≤ (33238638001163/100000000000000 : ℝ)^3899 := by
    have hnat : (2089839767 : ℕ)^4923*100000000000000^3899 ≤ 33238638001163^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089839767 5000000000 33238638001163 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2267058757/5000000000 : ℝ)^4923 ≤ (36836382380763/100000000000000 : ℝ)^3899 := by
    have hnat : (2267058757 : ℕ)^4923*100000000000000^3899 ≤ 36836382380763^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267058757 5000000000 36836382380763 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3846099563/10000000000 : ℝ)^4923 ≤ (14962489803997/50000000000000 : ℝ)^3899 := by
    have hnat : (3846099563 : ℕ)^4923*50000000000000^3899 ≤ 14962489803997^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3846099563 10000000000 14962489803997 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089839767/5000000000 : ℝ), (2267058757/5000000000 : ℝ), (3846099563/10000000000 : ℝ)] ![(33238638001163/100000000000000 : ℝ), (36836382380763/100000000000000 : ℝ), (14962489803997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089839767/5000000000 : ℝ)|^4923 ≤ (33238638001163/100000000000000 : ℝ)^3899
        have hw : |(2089839767/5000000000 : ℝ)|=(2089839767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2267058757/5000000000 : ℝ)|^4923 ≤ (36836382380763/100000000000000 : ℝ)^3899
        have hw : |(2267058757/5000000000 : ℝ)|=(2267058757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3846099563/10000000000 : ℝ)|^4923 ≤ (14962489803997/50000000000000 : ℝ)^3899
        have hw : |(3846099563/10000000000 : ℝ)|=(3846099563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1651_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8639/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9771/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10607/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8171/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8639/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9771/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8639/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9771/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8639/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9771/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8639/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9771/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8639/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9771/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8639/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9771/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9771/100000 : ℝ) ^ (4919/1024 : ℝ) ≤ (702957380285373/50000000000000000000 : ℝ) := by
    have hpowers : (9771/100000 : ℝ)^4919 ≤ (702957380285373/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9771 : ℕ)^4919*50000000000000000000^1024 ≤ 702957380285373^1024*100000^4919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9771 100000 702957380285373 50000000000000000000 4919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9771/100000 : ℝ)) (X := (702957380285373/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8639/50000 : ℝ) ^ (4919/1024 : ℝ) ≤ (10866984426397221/50000000000000000000 : ℝ) := by
    have hpowers : (8639/50000 : ℝ)^4919 ≤ (10866984426397221/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8639 : ℕ)^4919*50000000000000000000^1024 ≤ 10866984426397221^1024*50000^4919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8639 50000 10866984426397221 50000000000000000000 4919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8639/50000 : ℝ)) (X := (10866984426397221/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000702957380285373/25000000000000000000 : ℝ) ≤ (5000029266938163/5000000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (25000702957380285373/25000000000000000000 : ℝ)^1024 ≤ (5000029266938163/5000000000000000 : ℝ)^4919 := by
      have hnat : (25000702957380285373 : ℕ)^1024*5000000000000000^4919 ≤ 5000029266938163^4919*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000702957380285373 25000000000000000000 5000029266938163 5000000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000029266938163/5000000000000000 : ℝ)) (X := (25000702957380285373/25000000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25005784970903341297/25000000000000000000 : ℝ) ≤ (2000096332873773/2000000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (25005784970903341297/25000000000000000000 : ℝ)^1024 ≤ (2000096332873773/2000000000000000 : ℝ)^4919 := by
      have hnat : (25005784970903341297 : ℕ)^1024*2000000000000000^4919 ≤ 2000096332873773^4919*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005784970903341297 25000000000000000000 2000096332873773 2000000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000096332873773/2000000000000000 : ℝ)) (X := (25005784970903341297/25000000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010866984426397221/25000000000000000000 : ℝ) ≤ (2500226198715351/2500000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (25010866984426397221/25000000000000000000 : ℝ)^1024 ≤ (2500226198715351/2500000000000000 : ℝ)^4919 := by
      have hnat : (25010866984426397221 : ℕ)^1024*2500000000000000^4919 ≤ 2500226198715351^4919*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010866984426397221 25000000000000000000 2500226198715351 2500000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500226198715351/2500000000000000 : ℝ)) (X := (25010866984426397221/25000000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(702957380285373/50000000000000000000 : ℝ) ≤ ((1172846415589443471/1172968750000000000 : ℝ)+2*(423130492539/750700000000000 : ℝ)*(9771/100000 : ℝ))^(4919/1024 : ℝ) := by
    rw [show (1172846415589443471/1172968750000000000 : ℝ)+2*(423130492539/750700000000000 : ℝ)*(9771/100000 : ℝ)=(5000029266938163/5000000000000000 : ℝ) by norm_num, show 1+2*(702957380285373/50000000000000000000 : ℝ)=(25000702957380285373/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10866984426397221/50000000000000000000 : ℝ)+(702957380285373/50000000000000000000 : ℝ) ≤ ((1172846415589443471/1172968750000000000 : ℝ)+(423130492539/750700000000000 : ℝ)*((8639/50000 : ℝ)+(9771/100000 : ℝ)))^(4919/1024 : ℝ) := by
    rw [show (1172846415589443471/1172968750000000000 : ℝ)+(423130492539/750700000000000 : ℝ)*((8639/50000 : ℝ)+(9771/100000 : ℝ))=(2000096332873773/2000000000000000 : ℝ) by norm_num, show 1+(10866984426397221/50000000000000000000 : ℝ)+(702957380285373/50000000000000000000 : ℝ)=(25005784970903341297/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10866984426397221/50000000000000000000 : ℝ) ≤ ((1172846415589443471/1172968750000000000 : ℝ)+2*(423130492539/750700000000000 : ℝ)*(8639/50000 : ℝ))^(4919/1024 : ℝ) := by
    rw [show (1172846415589443471/1172968750000000000 : ℝ)+2*(423130492539/750700000000000 : ℝ)*(8639/50000 : ℝ)=(2500226198715351/2500000000000000 : ℝ) by norm_num, show 1+2*(10866984426397221/50000000000000000000 : ℝ)=(25010866984426397221/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1172846415589443471/1172968750000000000 : ℝ)*(X 1 0+X 2 0)+(423130492539/750700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (9771/100000 : ℝ)) (hi := (8639/50000 : ℝ)) (c := (1172846415589443471/1172968750000000000 : ℝ)) (alpha := (423130492539/750700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1172846415589443471/1172968750000000000 : ℝ)*(X 0 1+X 2 1)+(423130492539/750700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (9771/100000 : ℝ)) (hi := (8639/50000 : ℝ)) (c := (1172846415589443471/1172968750000000000 : ℝ)) (alpha := (423130492539/750700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1172846415589443471/1172968750000000000 : ℝ)*(X 0 2+X 1 2)+(423130492539/750700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (9771/100000 : ℝ)) (hi := (8639/50000 : ℝ)) (c := (1172846415589443471/1172968750000000000 : ℝ)) (alpha := (423130492539/750700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-802788449/5000000000 : ℝ)*X 0 0+(681341571/1250000000 : ℝ)*X 0 1+(2590466051/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348535007/10000000000 : ℝ)*X 1 0+(-436140127/2500000000 : ℝ)*X 1 1+(647616623/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334283519/625000000 : ℝ)*X 2 0+(5180931933/10000000000 : ℝ)*X 2 1+(-872280083/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2089750243/5000000000 : ℝ)*X 0 0+(3840619639/10000000000 : ℝ)*X 0 1+(4539539059/10000000000 : ℝ)*X 0 2+(2089750243/5000000000 : ℝ)*X 1 0+(3840619639/10000000000 : ℝ)*X 1 1+(4539539059/10000000000 : ℝ)*X 1 2+(2089750243/5000000000 : ℝ)*X 2 0+(3840619639/10000000000 : ℝ)*X 2 1+(4539539059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-802822653/5000000000 : ℝ)*X 0 0+(5183025441/10000000000 : ℝ)*X 0 1+(5448617111/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276445037/10000000000 : ℝ)*X 1 0+(-1476875431/10000000000 : ℝ)*X 1 1+(5448617051/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638222681/5000000000 : ℝ)*X 2 0+(5448616633/10000000000 : ℝ)*X 2 1+(-738437783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2089839767/5000000000 : ℝ)*X 0 0+(2267058757/5000000000 : ℝ)*X 0 1+(3846099563/10000000000 : ℝ)*X 0 2+(2089839767/5000000000 : ℝ)*X 1 0+(2267058757/5000000000 : ℝ)*X 1 1+(3846099563/10000000000 : ℝ)*X 1 2+(2089839767/5000000000 : ℝ)*X 2 0+(2267058757/5000000000 : ℝ)*X 2 1+(3846099563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8053450433531487065408043/916381835937500000000000000000 : ℝ) := by norm_num
    linear_combination (962610067/100000000000000 : ℝ)*(base19) + (322370777/20000000000000 : ℝ)*(base23) + (126733597/100000000000000 : ℝ)*(upper3) + (133480029/100000000000000 : ℝ)*(upper4) + (176041033/50000000000000 : ℝ)*(upper5) + (256863645028683/10000000000000 : ℝ)*(major0) + (256863645028683/10000000000000 : ℝ)*(major1) + (2568636450286831/100000000000000 : ℝ)*(major2) + (3706456046249513/100000000000000 : ℝ)*(sp0) + (1853239945694319/50000000000000 : ℝ)*(sp1) + (185323962107241/5000000000000 : ℝ)*(sp2) + (357696444222621/25000000000000 : ℝ)*(sp3) + (3100968649/12500000000000 : ℝ)*(sp4) + (2988370347/50000000000000 : ℝ)*(sp7) + (715395876815589/50000000000000 : ℝ)*(f.failure) + (1853240426999353/50000000000000 : ℝ)*(f.sum) + (162542531322301/75070000000000000000000000000 : ℝ)*base66 + (370491656391342103/46918750000000000000000000000000 : ℝ)*base68 + (570057517998279263/58648437500000000000000000000000 : ℝ)*base69 + (272629430264254603/46918750000000000000000000000000 : ℝ)*base72 + (264857948716881/75070000000000000000000000000 : ℝ)*base74 + (133044927212308097/14662109375000000000000000000000 : ℝ)*base75 + (99158145188226989/23459375000000000000000000000000 : ℝ)*base78 + (103319602593426989/23459375000000000000000000000000 : ℝ)*base80 + (79831254323/469187500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (9231999/625000000000000000000 : ℝ)*base89 + (9231999/625000000000000000000 : ℝ)*base91 + (2981999/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (535523478328430293118473443/117296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (461428687/100000000000000 : ℝ)*(base19) + (113474563/12500000000000 : ℝ)*(base23) + (26736783/100000000000000 : ℝ)*(upper3) + (108030907/100000000000000 : ℝ)*(lower4) + (5194869/12500000000000 : ℝ)*(upper5) + (326164262993623/12500000000000 : ℝ)*(major0) + (326164262993623/12500000000000 : ℝ)*(major1) + (326164262993623/12500000000000 : ℝ)*(major2) + (3001411649/50000000000000 : ℝ)*(sp1) + (6713562191/100000000000000 : ℝ)*(sp2) + (1882588939503493/50000000000000 : ℝ)*(sp4) + (1882585707377501/50000000000000 : ℝ)*(sp5) + (3765170257648291/100000000000000 : ℝ)*(sp6) + (1453450176706337/100000000000000 : ℝ)*(sp7) + (1453450176706337/100000000000000 : ℝ)*(f.failure) + (1882588939503493/50000000000000 : ℝ)*(f.sum) + (28409247209047/18767500000000000000000000000 : ℝ)*base66 + (12318917739869279/7331054687500000000000000000000 : ℝ)*base67 + (632591029528200911/117296875000000000000000000000000 : ℝ)*base70 + (331647150358530143/58648437500000000000000000000000 : ℝ)*base72 + (36276988664089/9383750000000000000000000000 : ℝ)*base73 + (1454661824844075911/117296875000000000000000000000000 : ℝ)*base76 + (32199999192005721/7331054687500000000000000000000 : ℝ)*base78 + (99844977556382259/29324218750000000000000000000000 : ℝ)*base80 + (141583412458289/37535000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6358867/1250000000000000000000 : ℝ)*base89 + (6358867/1250000000000000000000 : ℝ)*base91 + (6358867/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1651_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8639/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9771/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10607/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1651_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1651_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10607/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1651_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1651_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1651_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10607/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1651_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
