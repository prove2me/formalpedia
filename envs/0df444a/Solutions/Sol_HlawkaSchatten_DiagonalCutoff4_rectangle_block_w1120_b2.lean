-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1120_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:09:00.50625+00:00
-- url     : https://prove2.me/submissions/20925b19-8150-473d-aafd-00e5d35e78d7

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
theorem support_rectangle_w1120_s6_0 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-544354423/2500000000 : ℝ)*x 0 + (5393825171/10000000000 : ℝ)*x 1 + (2632501593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544354423/2500000000 : ℝ)^8313 ≤ (3307180700993/25000000000000 : ℝ)^6265 := by
    have hnat : (544354423 : ℕ)^8313*25000000000000^6265 ≤ 3307180700993^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544354423 2500000000 3307180700993 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393825171/10000000000 : ℝ)^8313 ≤ (44081378851037/100000000000000 : ℝ)^6265 := by
    have hnat : (5393825171 : ℕ)^8313*100000000000000^6265 ≤ 44081378851037^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393825171 10000000000 44081378851037 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632501593/5000000000 : ℝ)^8313 ≤ (42689898338079/100000000000000 : ℝ)^6265 := by
    have hnat : (2632501593 : ℕ)^8313*100000000000000^6265 ≤ 42689898338079^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632501593 5000000000 42689898338079 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-544354423/2500000000 : ℝ), (5393825171/10000000000 : ℝ), (2632501593/5000000000 : ℝ)] ![(3307180700993/25000000000000 : ℝ), (44081378851037/100000000000000 : ℝ), (42689898338079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-544354423/2500000000 : ℝ)|^8313 ≤ (3307180700993/25000000000000 : ℝ)^6265
        have hw : |(-544354423/2500000000 : ℝ)|=(544354423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393825171/10000000000 : ℝ)|^8313 ≤ (44081378851037/100000000000000 : ℝ)^6265
        have hw : |(5393825171/10000000000 : ℝ)|=(5393825171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632501593/5000000000 : ℝ)|^8313 ≤ (42689898338079/100000000000000 : ℝ)^6265
        have hw : |(2632501593/5000000000 : ℝ)|=(2632501593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s6_1 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068986737/2000000000 : ℝ)*x 0 + (-1121384829/5000000000 : ℝ)*x 1 + (5265003221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068986737/2000000000 : ℝ)^8313 ≤ (10887994989921/25000000000000 : ℝ)^6265 := by
    have hnat : (1068986737 : ℕ)^8313*25000000000000^6265 ≤ 10887994989921^6265*2000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068986737 2000000000 10887994989921 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121384829/5000000000 : ℝ)^8313 ≤ (1719765164273/12500000000000 : ℝ)^6265 := by
    have hnat : (1121384829 : ℕ)^8313*12500000000000^6265 ≤ 1719765164273^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121384829 5000000000 1719765164273 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265003221/10000000000 : ℝ)^8313 ≤ (42689898714637/100000000000000 : ℝ)^6265 := by
    have hnat : (5265003221 : ℕ)^8313*100000000000000^6265 ≤ 42689898714637^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265003221 10000000000 42689898714637 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068986737/2000000000 : ℝ), (-1121384829/5000000000 : ℝ), (5265003221/10000000000 : ℝ)] ![(10887994989921/25000000000000 : ℝ), (1719765164273/12500000000000 : ℝ), (42689898714637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068986737/2000000000 : ℝ)|^8313 ≤ (10887994989921/25000000000000 : ℝ)^6265
        have hw : |(1068986737/2000000000 : ℝ)|=(1068986737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1121384829/5000000000 : ℝ)|^8313 ≤ (1719765164273/12500000000000 : ℝ)^6265
        have hw : |(-1121384829/5000000000 : ℝ)|=(1121384829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265003221/10000000000 : ℝ)|^8313 ≤ (42689898714637/100000000000000 : ℝ)^6265
        have hw : |(5265003221/10000000000 : ℝ)|=(5265003221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s6_2 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672466817/5000000000 : ℝ)*x 0 + (5265003281/10000000000 : ℝ)*x 1 + (-2242769647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672466817/5000000000 : ℝ)^8313 ≤ (43551979408277/100000000000000 : ℝ)^6265 := by
    have hnat : (2672466817 : ℕ)^8313*100000000000000^6265 ≤ 43551979408277^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672466817 5000000000 43551979408277 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265003281/10000000000 : ℝ)^8313 ≤ (10672474840041/25000000000000 : ℝ)^6265 := by
    have hnat : (5265003281 : ℕ)^8313*25000000000000^6265 ≤ 10672474840041^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265003281 10000000000 10672474840041 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242769647/10000000000 : ℝ)^8313 ≤ (6879060612323/50000000000000 : ℝ)^6265 := by
    have hnat : (2242769647 : ℕ)^8313*50000000000000^6265 ≤ 6879060612323^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242769647 10000000000 6879060612323 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672466817/5000000000 : ℝ), (5265003281/10000000000 : ℝ), (-2242769647/10000000000 : ℝ)] ![(43551979408277/100000000000000 : ℝ), (10672474840041/25000000000000 : ℝ), (6879060612323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672466817/5000000000 : ℝ)|^8313 ≤ (43551979408277/100000000000000 : ℝ)^6265
        have hw : |(2672466817/5000000000 : ℝ)|=(2672466817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265003281/10000000000 : ℝ)|^8313 ≤ (10672474840041/25000000000000 : ℝ)^6265
        have hw : |(5265003281/10000000000 : ℝ)|=(5265003281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2242769647/10000000000 : ℝ)|^8313 ≤ (6879060612323/50000000000000 : ℝ)^6265
        have hw : |(-2242769647/10000000000 : ℝ)|=(2242769647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s6_3 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (27298513/62500000 : ℝ)*x 0 + (848406973/2000000000 : ℝ)*x 1 + (4497217187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27298513/62500000 : ℝ)^8313 ≤ (6663329109859/20000000000000 : ℝ)^6265 := by
    have hnat : (27298513 : ℕ)^8313*20000000000000^6265 ≤ 6663329109859^6265*62500000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27298513 62500000 6663329109859 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848406973/2000000000 : ℝ)^8313 ≤ (32050141024129/100000000000000 : ℝ)^6265 := by
    have hnat : (848406973 : ℕ)^8313*100000000000000^6265 ≤ 32050141024129^6265*2000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848406973 2000000000 32050141024129 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497217187/10000000000 : ℝ)^8313 ≤ (3463321340229/10000000000000 : ℝ)^6265 := by
    have hnat : (4497217187 : ℕ)^8313*10000000000000^6265 ≤ 3463321340229^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497217187 10000000000 3463321340229 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27298513/62500000 : ℝ), (848406973/2000000000 : ℝ), (4497217187/10000000000 : ℝ)] ![(6663329109859/20000000000000 : ℝ), (32050141024129/100000000000000 : ℝ), (3463321340229/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27298513/62500000 : ℝ)|^8313 ≤ (6663329109859/20000000000000 : ℝ)^6265
        have hw : |(27298513/62500000 : ℝ)|=(27298513/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(848406973/2000000000 : ℝ)|^8313 ≤ (32050141024129/100000000000000 : ℝ)^6265
        have hw : |(848406973/2000000000 : ℝ)|=(848406973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497217187/10000000000 : ℝ)|^8313 ≤ (3463321340229/10000000000000 : ℝ)^6265
        have hw : |(4497217187/10000000000 : ℝ)|=(4497217187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s6_4 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2177422811/10000000000 : ℝ)*x 0 + (1316332123/2500000000 : ℝ)*x 1 + (5393498613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177422811/10000000000 : ℝ)^8313 ≤ (6614382035261/50000000000000 : ℝ)^6265 := by
    have hnat : (2177422811 : ℕ)^8313*50000000000000^6265 ≤ 6614382035261^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177422811 10000000000 6614382035261 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316332123/2500000000 : ℝ)^8313 ≤ (42693398270403/100000000000000 : ℝ)^6265 := by
    have hnat : (1316332123 : ℕ)^8313*100000000000000^6265 ≤ 42693398270403^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316332123 2500000000 42693398270403 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393498613/10000000000 : ℝ)^8313 ≤ (44077837646271/100000000000000 : ℝ)^6265 := by
    have hnat : (5393498613 : ℕ)^8313*100000000000000^6265 ≤ 44077837646271^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393498613 10000000000 44077837646271 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2177422811/10000000000 : ℝ), (1316332123/2500000000 : ℝ), (5393498613/10000000000 : ℝ)] ![(6614382035261/50000000000000 : ℝ), (42693398270403/100000000000000 : ℝ), (44077837646271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2177422811/10000000000 : ℝ)|^8313 ≤ (6614382035261/50000000000000 : ℝ)^6265
        have hw : |(-2177422811/10000000000 : ℝ)|=(2177422811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316332123/2500000000 : ℝ)|^8313 ≤ (42693398270403/100000000000000 : ℝ)^6265
        have hw : |(1316332123/2500000000 : ℝ)|=(1316332123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393498613/10000000000 : ℝ)|^8313 ≤ (44077837646271/100000000000000 : ℝ)^6265
        have hw : |(5393498613/10000000000 : ℝ)|=(5393498613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s6_5 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531234987/1000000000 : ℝ)*x 0 + (-1057137137/5000000000 : ℝ)*x 1 + (5393498593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531234987/1000000000 : ℝ)^8313 ≤ (21600019151763/50000000000000 : ℝ)^6265 := by
    have hnat : (531234987 : ℕ)^8313*50000000000000^6265 ≤ 21600019151763^6265*1000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531234987 1000000000 21600019151763 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057137137/5000000000 : ℝ)^8313 ≤ (3180531061279/25000000000000 : ℝ)^6265 := by
    have hnat : (1057137137 : ℕ)^8313*25000000000000^6265 ≤ 3180531061279^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057137137 5000000000 3180531061279 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393498593/10000000000 : ℝ)^8313 ≤ (44077837429393/100000000000000 : ℝ)^6265 := by
    have hnat : (5393498593 : ℕ)^8313*100000000000000^6265 ≤ 44077837429393^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393498593 10000000000 44077837429393 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531234987/1000000000 : ℝ), (-1057137137/5000000000 : ℝ), (5393498593/10000000000 : ℝ)] ![(21600019151763/50000000000000 : ℝ), (3180531061279/25000000000000 : ℝ), (44077837429393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531234987/1000000000 : ℝ)|^8313 ≤ (21600019151763/50000000000000 : ℝ)^6265
        have hw : |(531234987/1000000000 : ℝ)|=(531234987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1057137137/5000000000 : ℝ)|^8313 ≤ (3180531061279/25000000000000 : ℝ)^6265
        have hw : |(-1057137137/5000000000 : ℝ)|=(1057137137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393498593/10000000000 : ℝ)|^8313 ≤ (44077837429393/100000000000000 : ℝ)^6265
        have hw : |(5393498593/10000000000 : ℝ)|=(5393498593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s6_6 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312349909/10000000000 : ℝ)*x 0 + (5393498511/10000000000 : ℝ)*x 1 + (-1057137167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312349909/10000000000 : ℝ)^8313 ≤ (43200038724349/100000000000000 : ℝ)^6265 := by
    have hnat : (5312349909 : ℕ)^8313*100000000000000^6265 ≤ 43200038724349^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312349909 10000000000 43200038724349 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393498511/10000000000 : ℝ)^8313 ≤ (44077836540191/100000000000000 : ℝ)^6265 := by
    have hnat : (5393498511 : ℕ)^8313*100000000000000^6265 ≤ 44077836540191^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393498511 10000000000 44077836540191 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057137167/5000000000 : ℝ)^8313 ≤ (3180531181043/25000000000000 : ℝ)^6265 := by
    have hnat : (1057137167 : ℕ)^8313*25000000000000^6265 ≤ 3180531181043^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057137167 5000000000 3180531181043 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312349909/10000000000 : ℝ), (5393498511/10000000000 : ℝ), (-1057137167/5000000000 : ℝ)] ![(43200038724349/100000000000000 : ℝ), (44077836540191/100000000000000 : ℝ), (3180531181043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312349909/10000000000 : ℝ)|^8313 ≤ (43200038724349/100000000000000 : ℝ)^6265
        have hw : |(5312349909/10000000000 : ℝ)|=(5312349909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393498511/10000000000 : ℝ)|^8313 ≤ (44077836540191/100000000000000 : ℝ)^6265
        have hw : |(5393498511/10000000000 : ℝ)|=(5393498511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1057137167/5000000000 : ℝ)|^8313 ≤ (3180531181043/25000000000000 : ℝ)^6265
        have hw : |(-1057137167/5000000000 : ℝ)|=(1057137167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s6_7 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183885989/5000000000 : ℝ)*x 0 + (4496572769/10000000000 : ℝ)*x 1 + (1060670421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183885989/5000000000 : ℝ)^8313 ≤ (33316745730583/100000000000000 : ℝ)^6265 := by
    have hnat : (2183885989 : ℕ)^8313*100000000000000^6265 ≤ 33316745730583^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183885989 5000000000 33316745730583 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496572769/10000000000 : ℝ)^8313 ≤ (34626628594187/100000000000000 : ℝ)^6265 := by
    have hnat : (4496572769 : ℕ)^8313*100000000000000^6265 ≤ 34626628594187^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496572769 10000000000 34626628594187 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060670421/2500000000 : ℝ)^8313 ≤ (32056625666177/100000000000000 : ℝ)^6265 := by
    have hnat : (1060670421 : ℕ)^8313*100000000000000^6265 ≤ 32056625666177^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060670421 2500000000 32056625666177 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183885989/5000000000 : ℝ), (4496572769/10000000000 : ℝ), (1060670421/2500000000 : ℝ)] ![(33316745730583/100000000000000 : ℝ), (34626628594187/100000000000000 : ℝ), (32056625666177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183885989/5000000000 : ℝ)|^8313 ≤ (33316745730583/100000000000000 : ℝ)^6265
        have hw : |(2183885989/5000000000 : ℝ)|=(2183885989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496572769/10000000000 : ℝ)|^8313 ≤ (34626628594187/100000000000000 : ℝ)^6265
        have hw : |(4496572769/10000000000 : ℝ)|=(4496572769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060670421/2500000000 : ℝ)|^8313 ≤ (32056625666177/100000000000000 : ℝ)^6265
        have hw : |(1060670421/2500000000 : ℝ)|=(1060670421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1120_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2829/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2809/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5641/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5641/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5641/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5641/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5641/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5641/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5641/50000 : ℝ) ^ (1039/256 : ℝ) ≤ (7128368356698343/50000000000000000000 : ℝ) := by
    have hpowers : (5641/50000 : ℝ)^1039 ≤ (7128368356698343/50000000000000000000 : ℝ)^256 := by
      have hnat : (5641 : ℕ)^1039*50000000000000000000^256 ≤ 7128368356698343^256*50000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5641 50000 7128368356698343 50000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5641/50000 : ℝ)) (X := (7128368356698343/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hpowhi : (88/625 : ℝ) ^ (1039/256 : ℝ) ≤ (35036769500025841/100000000000000000000 : ℝ) := by
    have hpowers : (88/625 : ℝ)^1039 ≤ (35036769500025841/100000000000000000000 : ℝ)^256 := by
      have hnat : (88 : ℕ)^1039*100000000000000000000^256 ≤ 35036769500025841^256*625^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88 625 35036769500025841 100000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88/625 : ℝ)) (X := (35036769500025841/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007128368356698343/25000000000000000000 : ℝ) ≤ (1000070247017079/1000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (25007128368356698343/25000000000000000000 : ℝ)^256 ≤ (1000070247017079/1000000000000000 : ℝ)^1039 := by
      have hnat : (25007128368356698343 : ℕ)^256*1000000000000000^1039 ≤ 1000070247017079^1039*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007128368356698343 25000000000000000000 1000070247017079 1000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000070247017079/1000000000000000 : ℝ)) (X := (25007128368356698343/25000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049293506213422527/100000000000000000000 : ℝ) ≤ (2500303580230619/2500000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (100049293506213422527/100000000000000000000 : ℝ)^256 ≤ (2500303580230619/2500000000000000 : ℝ)^1039 := by
      have hnat : (100049293506213422527 : ℕ)^256*2500000000000000^1039 ≤ 2500303580230619^1039*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049293506213422527 100000000000000000000 2500303580230619 2500000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500303580230619/2500000000000000 : ℝ)) (X := (100049293506213422527/100000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035036769500025841/50000000000000000000 : ℝ) ≤ (5000863085837081/5000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (50035036769500025841/50000000000000000000 : ℝ)^256 ≤ (5000863085837081/5000000000000000 : ℝ)^1039 := by
      have hnat : (50035036769500025841 : ℕ)^256*5000000000000000^1039 ≤ 5000863085837081^1039*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035036769500025841 50000000000000000000 5000863085837081 5000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000863085837081/5000000000000000 : ℝ)) (X := (50035036769500025841/50000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7128368356698343/50000000000000000000 : ℝ) ≤ ((6992604027794206879/6995000000000000000 : ℝ)+2*(255925375843/139900000000000 : ℝ)*(5641/50000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (6992604027794206879/6995000000000000000 : ℝ)+2*(255925375843/139900000000000 : ℝ)*(5641/50000 : ℝ)=(1000070247017079/1000000000000000 : ℝ) by norm_num, show 1+2*(7128368356698343/50000000000000000000 : ℝ)=(25007128368356698343/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35036769500025841/100000000000000000000 : ℝ)+(7128368356698343/50000000000000000000 : ℝ) ≤ ((6992604027794206879/6995000000000000000 : ℝ)+(255925375843/139900000000000 : ℝ)*((88/625 : ℝ)+(5641/50000 : ℝ)))^(1039/256 : ℝ) := by
    rw [show (6992604027794206879/6995000000000000000 : ℝ)+(255925375843/139900000000000 : ℝ)*((88/625 : ℝ)+(5641/50000 : ℝ))=(2500303580230619/2500000000000000 : ℝ) by norm_num, show 1+(35036769500025841/100000000000000000000 : ℝ)+(7128368356698343/50000000000000000000 : ℝ)=(100049293506213422527/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35036769500025841/100000000000000000000 : ℝ) ≤ ((6992604027794206879/6995000000000000000 : ℝ)+2*(255925375843/139900000000000 : ℝ)*(88/625 : ℝ))^(1039/256 : ℝ) := by
    rw [show (6992604027794206879/6995000000000000000 : ℝ)+2*(255925375843/139900000000000 : ℝ)*(88/625 : ℝ)=(5000863085837081/5000000000000000 : ℝ) by norm_num, show 1+2*(35036769500025841/100000000000000000000 : ℝ)=(50035036769500025841/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6992604027794206879/6995000000000000000 : ℝ)*(X 1 0+X 2 0)+(255925375843/139900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (5641/50000 : ℝ)) (hi := (88/625 : ℝ)) (c := (6992604027794206879/6995000000000000000 : ℝ)) (alpha := (255925375843/139900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6992604027794206879/6995000000000000000 : ℝ)*(X 0 1+X 2 1)+(255925375843/139900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (5641/50000 : ℝ)) (hi := (88/625 : ℝ)) (c := (6992604027794206879/6995000000000000000 : ℝ)) (alpha := (255925375843/139900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6992604027794206879/6995000000000000000 : ℝ)*(X 0 2+X 1 2)+(255925375843/139900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (5641/50000 : ℝ)) (hi := (88/625 : ℝ)) (c := (6992604027794206879/6995000000000000000 : ℝ)) (alpha := (255925375843/139900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-544354423/2500000000 : ℝ)*X 0 0+(5393825171/10000000000 : ℝ)*X 0 1+(2632501593/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068986737/2000000000 : ℝ)*X 1 0+(-1121384829/5000000000 : ℝ)*X 1 1+(5265003221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672466817/5000000000 : ℝ)*X 2 0+(5265003281/10000000000 : ℝ)*X 2 1+(-2242769647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((27298513/62500000 : ℝ)*X 0 0+(848406973/2000000000 : ℝ)*X 0 1+(4497217187/10000000000 : ℝ)*X 0 2+(27298513/62500000 : ℝ)*X 1 0+(848406973/2000000000 : ℝ)*X 1 1+(4497217187/10000000000 : ℝ)*X 1 2+(27298513/62500000 : ℝ)*X 2 0+(848406973/2000000000 : ℝ)*X 2 1+(4497217187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2177422811/10000000000 : ℝ)*X 0 0+(1316332123/2500000000 : ℝ)*X 0 1+(5393498613/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531234987/1000000000 : ℝ)*X 1 0+(-1057137137/5000000000 : ℝ)*X 1 1+(5393498593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312349909/10000000000 : ℝ)*X 2 0+(5393498511/10000000000 : ℝ)*X 2 1+(-1057137167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2183885989/5000000000 : ℝ)*X 0 0+(4496572769/10000000000 : ℝ)*X 0 1+(1060670421/2500000000 : ℝ)*X 0 2+(2183885989/5000000000 : ℝ)*X 1 0+(4496572769/10000000000 : ℝ)*X 1 1+(1060670421/2500000000 : ℝ)*X 1 2+(2183885989/5000000000 : ℝ)*X 2 0+(4496572769/10000000000 : ℝ)*X 2 1+(1060670421/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3991093087551372972437547/546484375000000000000000000000 : ℝ) := by norm_num
    linear_combination (93815261/6250000000000 : ℝ)*(base19) + (156445007/12500000000000 : ℝ)*(base23) + (93757663/100000000000000 : ℝ)*(lower2) + (107516557/50000000000000 : ℝ)*(upper3) + (11109959/12500000000000 : ℝ)*(upper5) + (18252409835569/312500000000 : ℝ)*(major0) + (18252409835569/312500000000 : ℝ)*(major1) + (18252409835569/312500000000 : ℝ)*(major2) + (970336858221833/12500000000000 : ℝ)*(sp0) + (1940683514314933/25000000000000 : ℝ)*(sp1) + (1940683576685963/25000000000000 : ℝ)*(sp2) + (979696256766337/25000000000000 : ℝ)*(sp3) + (10173132311/25000000000000 : ℝ)*(sp4) + (1341622149/6250000000000 : ℝ)*(sp7) + (979701623254933/25000000000000 : ℝ)*(f.failure) + (1940683889575977/25000000000000 : ℝ)*(f.sum) + (176998076427/349750000000000000000000000 : ℝ)*base65 + (10307895491572901/2185937500000000000000000000000 : ℝ)*base67 + (40050106713291651/2185937500000000000000000000000 : ℝ)*base69 + (5934899315485401/2185937500000000000000000000000 : ℝ)*base71 + (632931952587/349750000000000000000000000 : ℝ)*base73 + (8301909842495849/2185937500000000000000000000000 : ℝ)*base76 + (12019137750716651/2185937500000000000000000000000 : ℝ)*base77 + (27504904464729151/2185937500000000000000000000000 : ℝ)*base79 + (54175085753/174875000000000000000000000 : ℝ)*base82 + (13026081/2500000000000000000000 : ℝ)*base90 + (13026081/2500000000000000000000 : ℝ)*base92 + (13026081/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (710269478931237765790555917/87437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (899684793/50000000000000 : ℝ)*(base19) + (1830490483/100000000000000 : ℝ)*(base23) + (80493251/50000000000000 : ℝ)*(upper3) + (4523983/100000000000000 : ℝ)*(lower4) + (56218127/25000000000000 : ℝ)*(upper5) + (1467603678157353/25000000000000 : ℝ)*(major0) + (1467603678157353/25000000000000 : ℝ)*(major1) + (1467603678157353/25000000000000 : ℝ)*(major2) + (50763624691/100000000000000 : ℝ)*(sp1) + (45110701281/100000000000000 : ℝ)*(sp2) + (7802133610340491/100000000000000 : ℝ)*(sp4) + (7802081047346213/100000000000000 : ℝ)*(sp5) + (7802086669148727/100000000000000 : ℝ)*(sp6) + (1969347772073033/50000000000000 : ℝ)*(sp7) + (1969347772073033/50000000000000 : ℝ)*(f.failure) + (7802133610340491/100000000000000 : ℝ)*(f.sum) + (68313254657051/6995000000000000000000000000 : ℝ)*base65 + (344821852716731287/174875000000000000000000000000000 : ℝ)*base67 + (579145993516856287/174875000000000000000000000000000 : ℝ)*base69 + (2948491857350106287/174875000000000000000000000000000 : ℝ)*base71 + (5795300614943/3497500000000000000000000000 : ℝ)*base73 + (1753734320671481287/174875000000000000000000000000000 : ℝ)*base75 + (1019525763544106287/174875000000000000000000000000000 : ℝ)*base77 + (641343595027481287/174875000000000000000000000000000 : ℝ)*base79 + (11165740283911/6995000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (26587781/5000000000000000000000 : ℝ)*base90 + (26587781/5000000000000000000000 : ℝ)*base92 + (26587781/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1120_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2829/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1120_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1120_s7_0 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-272180863/1250000000 : ℝ)*x 0 + (5393467531/10000000000 : ℝ)*x 1 + (5265341767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272180863/1250000000 : ℝ)^8313 ≤ (826809893463/6250000000000 : ℝ)^6265 := by
    have hnat : (272180863 : ℕ)^8313*6250000000000^6265 ≤ 826809893463^6265*1250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272180863 1250000000 826809893463 6250000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393467531/10000000000 : ℝ)^8313 ≤ (22038750297891/50000000000000 : ℝ)^6265 := by
    have hnat : (5393467531 : ℕ)^8313*50000000000000^6265 ≤ 22038750297891^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393467531 10000000000 22038750297891 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265341767/10000000000 : ℝ)^8313 ≤ (10673385274051/25000000000000 : ℝ)^6265 := by
    have hnat : (5265341767 : ℕ)^8313*25000000000000^6265 ≤ 10673385274051^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265341767 10000000000 10673385274051 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272180863/1250000000 : ℝ), (5393467531/10000000000 : ℝ), (5265341767/10000000000 : ℝ)] ![(826809893463/6250000000000 : ℝ), (22038750297891/50000000000000 : ℝ), (10673385274051/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272180863/1250000000 : ℝ)|^8313 ≤ (826809893463/6250000000000 : ℝ)^6265
        have hw : |(-272180863/1250000000 : ℝ)|=(272180863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393467531/10000000000 : ℝ)|^8313 ≤ (22038750297891/50000000000000 : ℝ)^6265
        have hw : |(5393467531/10000000000 : ℝ)|=(5393467531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265341767/10000000000 : ℝ)|^8313 ≤ (10673385274051/25000000000000 : ℝ)^6265
        have hw : |(5265341767/10000000000 : ℝ)|=(5265341767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s7_1 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344844479/10000000000 : ℝ)*x 0 + (-2242440657/10000000000 : ℝ)*x 1 + (5265341769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344844479/10000000000 : ℝ)^8313 ≤ (4355101547537/10000000000000 : ℝ)^6265 := by
    have hnat : (5344844479 : ℕ)^8313*10000000000000^6265 ≤ 4355101547537^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344844479 10000000000 4355101547537 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242440657/10000000000 : ℝ)^8313 ≤ (13755443391881/100000000000000 : ℝ)^6265 := by
    have hnat : (2242440657 : ℕ)^8313*100000000000000^6265 ≤ 13755443391881^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242440657 10000000000 13755443391881 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265341769/10000000000 : ℝ)^8313 ≤ (21346770558861/50000000000000 : ℝ)^6265 := by
    have hnat : (5265341769 : ℕ)^8313*50000000000000^6265 ≤ 21346770558861^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265341769 10000000000 21346770558861 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344844479/10000000000 : ℝ), (-2242440657/10000000000 : ℝ), (5265341769/10000000000 : ℝ)] ![(4355101547537/10000000000000 : ℝ), (13755443391881/100000000000000 : ℝ), (21346770558861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344844479/10000000000 : ℝ)|^8313 ≤ (4355101547537/10000000000000 : ℝ)^6265
        have hw : |(5344844479/10000000000 : ℝ)|=(5344844479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2242440657/10000000000 : ℝ)|^8313 ≤ (13755443391881/100000000000000 : ℝ)^6265
        have hw : |(-2242440657/10000000000 : ℝ)|=(2242440657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265341769/10000000000 : ℝ)|^8313 ≤ (21346770558861/50000000000000 : ℝ)^6265
        have hw : |(5265341769/10000000000 : ℝ)|=(5265341769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s7_2 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344844479/10000000000 : ℝ)*x 0 + (526534177/1000000000 : ℝ)*x 1 + (-448488131/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344844479/10000000000 : ℝ)^8313 ≤ (4355101547537/10000000000000 : ℝ)^6265 := by
    have hnat : (5344844479 : ℕ)^8313*10000000000000^6265 ≤ 4355101547537^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344844479 10000000000 4355101547537 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526534177/1000000000 : ℝ)^8313 ≤ (42693541128481/100000000000000 : ℝ)^6265 := by
    have hnat : (526534177 : ℕ)^8313*100000000000000^6265 ≤ 42693541128481^6265*1000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526534177 1000000000 42693541128481 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448488131/2000000000 : ℝ)^8313 ≤ (6877721687801/50000000000000 : ℝ)^6265 := by
    have hnat : (448488131 : ℕ)^8313*50000000000000^6265 ≤ 6877721687801^6265*2000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448488131 2000000000 6877721687801 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344844479/10000000000 : ℝ), (526534177/1000000000 : ℝ), (-448488131/2000000000 : ℝ)] ![(4355101547537/10000000000000 : ℝ), (42693541128481/100000000000000 : ℝ), (6877721687801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344844479/10000000000 : ℝ)|^8313 ≤ (4355101547537/10000000000000 : ℝ)^6265
        have hw : |(5344844479/10000000000 : ℝ)|=(5344844479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526534177/1000000000 : ℝ)|^8313 ≤ (42693541128481/100000000000000 : ℝ)^6265
        have hw : |(526534177/1000000000 : ℝ)|=(526534177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-448488131/2000000000 : ℝ)|^8313 ≤ (6877721687801/50000000000000 : ℝ)^6265
        have hw : |(-448488131/2000000000 : ℝ)|=(448488131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s7_3 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367779779/10000000000 : ℝ)*x 0 + (1060680511/2500000000 : ℝ)*x 1 + (7025821/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367779779/10000000000 : ℝ)^8313 ≤ (33316824687417/100000000000000 : ℝ)^6265 := by
    have hnat : (4367779779 : ℕ)^8313*100000000000000^6265 ≤ 33316824687417^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367779779 10000000000 33316824687417 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060680511/2500000000 : ℝ)^8313 ≤ (32057030303459/100000000000000 : ℝ)^6265 := by
    have hnat : (1060680511 : ℕ)^8313*100000000000000^6265 ≤ 32057030303459^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060680511 2500000000 32057030303459 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7025821/15625000 : ℝ)^8313 ≤ (34626144987977/100000000000000 : ℝ)^6265 := by
    have hnat : (7025821 : ℕ)^8313*100000000000000^6265 ≤ 34626144987977^6265*15625000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7025821 15625000 34626144987977 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367779779/10000000000 : ℝ), (1060680511/2500000000 : ℝ), (7025821/15625000 : ℝ)] ![(33316824687417/100000000000000 : ℝ), (32057030303459/100000000000000 : ℝ), (34626144987977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367779779/10000000000 : ℝ)|^8313 ≤ (33316824687417/100000000000000 : ℝ)^6265
        have hw : |(4367779779/10000000000 : ℝ)|=(4367779779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060680511/2500000000 : ℝ)|^8313 ≤ (32057030303459/100000000000000 : ℝ)^6265
        have hw : |(1060680511/2500000000 : ℝ)|=(1060680511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7025821/15625000 : ℝ)|^8313 ≤ (34626144987977/100000000000000 : ℝ)^6265
        have hw : |(7025821/15625000 : ℝ)|=(7025821/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s7_4 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2177451851/10000000000 : ℝ)*x 0 + (1316415893/2500000000 : ℝ)*x 1 + (5393144561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177451851/10000000000 : ℝ)^8313 ≤ (3307249543891/25000000000000 : ℝ)^6265 := by
    have hnat : (2177451851 : ℕ)^8313*25000000000000^6265 ≤ 3307249543891^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177451851 10000000000 3307249543891 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316415893/2500000000 : ℝ)^8313 ≤ (42697003434049/100000000000000 : ℝ)^6265 := by
    have hnat : (1316415893 : ℕ)^8313*100000000000000^6265 ≤ 42697003434049^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316415893 2500000000 42697003434049 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393144561/10000000000 : ℝ)^8313 ≤ (44073998374931/100000000000000 : ℝ)^6265 := by
    have hnat : (5393144561 : ℕ)^8313*100000000000000^6265 ≤ 44073998374931^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393144561 10000000000 44073998374931 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2177451851/10000000000 : ℝ), (1316415893/2500000000 : ℝ), (5393144561/10000000000 : ℝ)] ![(3307249543891/25000000000000 : ℝ), (42697003434049/100000000000000 : ℝ), (44073998374931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2177451851/10000000000 : ℝ)|^8313 ≤ (3307249543891/25000000000000 : ℝ)^6265
        have hw : |(-2177451851/10000000000 : ℝ)|=(2177451851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316415893/2500000000 : ℝ)|^8313 ≤ (42697003434049/100000000000000 : ℝ)^6265
        have hw : |(1316415893/2500000000 : ℝ)|=(1316415893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393144561/10000000000 : ℝ)|^8313 ≤ (44073998374931/100000000000000 : ℝ)^6265
        have hw : |(5393144561/10000000000 : ℝ)|=(5393144561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s7_5 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664054579/1250000000 : ℝ)*x 0 + (-2114637863/10000000000 : ℝ)*x 1 + (2696572271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664054579/1250000000 : ℝ)^8313 ≤ (4320097449543/10000000000000 : ℝ)^6265 := by
    have hnat : (664054579 : ℕ)^8313*10000000000000^6265 ≤ 4320097449543^6265*1250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664054579 1250000000 4320097449543 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114637863/10000000000 : ℝ)^8313 ≤ (6362513659051/50000000000000 : ℝ)^6265 := by
    have hnat : (2114637863 : ℕ)^8313*50000000000000^6265 ≤ 6362513659051^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114637863 10000000000 6362513659051 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696572271/5000000000 : ℝ)^8313 ≤ (44073998168901/100000000000000 : ℝ)^6265 := by
    have hnat : (2696572271 : ℕ)^8313*100000000000000^6265 ≤ 44073998168901^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696572271 5000000000 44073998168901 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664054579/1250000000 : ℝ), (-2114637863/10000000000 : ℝ), (2696572271/5000000000 : ℝ)] ![(4320097449543/10000000000000 : ℝ), (6362513659051/50000000000000 : ℝ), (44073998168901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664054579/1250000000 : ℝ)|^8313 ≤ (4320097449543/10000000000000 : ℝ)^6265
        have hw : |(664054579/1250000000 : ℝ)|=(664054579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2114637863/10000000000 : ℝ)|^8313 ≤ (6362513659051/50000000000000 : ℝ)^6265
        have hw : |(-2114637863/10000000000 : ℝ)|=(2114637863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696572271/5000000000 : ℝ)|^8313 ≤ (44073998168901/100000000000000 : ℝ)^6265
        have hw : |(2696572271/5000000000 : ℝ)|=(2696572271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s7_6 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312436629/10000000000 : ℝ)*x 0 + (215725781/400000000 : ℝ)*x 1 + (-211463789/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312436629/10000000000 : ℝ)^8313 ≤ (43200974463059/100000000000000 : ℝ)^6265 := by
    have hnat : (5312436629 : ℕ)^8313*100000000000000^6265 ≤ 43200974463059^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312436629 10000000000 43200974463059 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215725781/400000000 : ℝ)^8313 ≤ (44073997984559/100000000000000 : ℝ)^6265 := by
    have hnat : (215725781 : ℕ)^8313*100000000000000^6265 ≤ 44073997984559^6265*400000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215725781 400000000 44073997984559 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211463789/1000000000 : ℝ)^8313 ≤ (12725027533689/100000000000000 : ℝ)^6265 := by
    have hnat : (211463789 : ℕ)^8313*100000000000000^6265 ≤ 12725027533689^6265*1000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211463789 1000000000 12725027533689 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312436629/10000000000 : ℝ), (215725781/400000000 : ℝ), (-211463789/1000000000 : ℝ)] ![(43200974463059/100000000000000 : ℝ), (44073997984559/100000000000000 : ℝ), (12725027533689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312436629/10000000000 : ℝ)|^8313 ≤ (43200974463059/100000000000000 : ℝ)^6265
        have hw : |(5312436629/10000000000 : ℝ)|=(5312436629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215725781/400000000 : ℝ)|^8313 ≤ (44073997984559/100000000000000 : ℝ)^6265
        have hw : |(215725781/400000000 : ℝ)|=(215725781/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-211463789/1000000000 : ℝ)|^8313 ≤ (12725027533689/100000000000000 : ℝ)^6265
        have hw : |(-211463789/1000000000 : ℝ)|=(211463789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s7_7 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367789557/10000000000 : ℝ)*x 0 + (280992997/625000000 : ℝ)*x 1 + (2121680927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367789557/10000000000 : ℝ)^8313 ≤ (260288466049/781250000000 : ℝ)^6265 := by
    have hnat : (4367789557 : ℕ)^8313*781250000000^6265 ≤ 260288466049^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367789557 10000000000 260288466049 781250000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280992997/625000000 : ℝ)^8313 ≤ (3461963131811/10000000000000 : ℝ)^6265 := by
    have hnat : (280992997 : ℕ)^8313*10000000000000^6265 ≤ 3461963131811^6265*625000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280992997 625000000 3461963131811 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121680927/5000000000 : ℝ)^8313 ≤ (16031722507563/50000000000000 : ℝ)^6265 := by
    have hnat : (2121680927 : ℕ)^8313*50000000000000^6265 ≤ 16031722507563^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121680927 5000000000 16031722507563 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367789557/10000000000 : ℝ), (280992997/625000000 : ℝ), (2121680927/5000000000 : ℝ)] ![(260288466049/781250000000 : ℝ), (3461963131811/10000000000000 : ℝ), (16031722507563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367789557/10000000000 : ℝ)|^8313 ≤ (260288466049/781250000000 : ℝ)^6265
        have hw : |(4367789557/10000000000 : ℝ)|=(4367789557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280992997/625000000 : ℝ)|^8313 ≤ (3461963131811/10000000000000 : ℝ)^6265
        have hw : |(280992997/625000000 : ℝ)|=(280992997/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121680927/5000000000 : ℝ)|^8313 ≤ (16031722507563/50000000000000 : ℝ)^6265
        have hw : |(2121680927/5000000000 : ℝ)|=(2121680927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1120_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2829/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11323/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14037/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2809/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2829/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2809/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2829/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2809/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2829/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2809/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2829/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2809/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2829/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2809/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2829/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2829/25000 : ℝ) ^ (1039/256 : ℝ) ≤ (288638375394577/2000000000000000000 : ℝ) := by
    have hpowers : (2829/25000 : ℝ)^1039 ≤ (288638375394577/2000000000000000000 : ℝ)^256 := by
      have hnat : (2829 : ℕ)^1039*2000000000000000000^256 ≤ 288638375394577^256*25000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2829 25000 288638375394577 2000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2829/25000 : ℝ)) (X := (288638375394577/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2809/20000 : ℝ) ^ (1039/256 : ℝ) ≤ (3468463082326711/10000000000000000000 : ℝ) := by
    have hpowers : (2809/20000 : ℝ)^1039 ≤ (3468463082326711/10000000000000000000 : ℝ)^256 := by
      have hnat : (2809 : ℕ)^1039*10000000000000000000^256 ≤ 3468463082326711^256*20000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2809 20000 3468463082326711 10000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2809/20000 : ℝ)) (X := (3468463082326711/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000288638375394577/1000000000000000000 : ℝ) ≤ (1000071110095289/1000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (1000288638375394577/1000000000000000000 : ℝ)^256 ≤ (1000071110095289/1000000000000000 : ℝ)^1039 := by
      have hnat : (1000288638375394577 : ℕ)^256*1000000000000000^1039 ≤ 1000071110095289^1039*1000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000288638375394577 1000000000000000000 1000071110095289 1000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000071110095289/1000000000000000 : ℝ)) (X := (1000288638375394577/1000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501227913739824899/2500000000000000000 : ℝ) ≤ (5000604981245459/5000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (2501227913739824899/2500000000000000000 : ℝ)^256 ≤ (5000604981245459/5000000000000000 : ℝ)^1039 := by
      have hnat : (2501227913739824899 : ℕ)^256*5000000000000000^1039 ≤ 5000604981245459^1039*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501227913739824899 2500000000000000000 5000604981245459 5000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000604981245459/5000000000000000 : ℝ)) (X := (2501227913739824899/2500000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003468463082326711/5000000000000000000 : ℝ) ≤ (5000854412014473/5000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (5003468463082326711/5000000000000000000 : ℝ)^256 ≤ (5000854412014473/5000000000000000 : ℝ)^1039 := by
      have hnat : (5003468463082326711 : ℕ)^256*5000000000000000^1039 ≤ 5000854412014473^1039*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003468463082326711 5000000000000000000 5000854412014473 5000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000854412014473/5000000000000000 : ℝ)) (X := (5003468463082326711/5000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(288638375394577/2000000000000000000 : ℝ) ≤ ((13640325180085893557/13645000000000000000 : ℝ)+2*(124715384507/68225000000000 : ℝ)*(2829/25000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (13640325180085893557/13645000000000000000 : ℝ)+2*(124715384507/68225000000000 : ℝ)*(2829/25000 : ℝ)=(1000071110095289/1000000000000000 : ℝ) by norm_num, show 1+2*(288638375394577/2000000000000000000 : ℝ)=(1000288638375394577/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3468463082326711/10000000000000000000 : ℝ)+(288638375394577/2000000000000000000 : ℝ) ≤ ((13640325180085893557/13645000000000000000 : ℝ)+(124715384507/68225000000000 : ℝ)*((2809/20000 : ℝ)+(2829/25000 : ℝ)))^(1039/256 : ℝ) := by
    rw [show (13640325180085893557/13645000000000000000 : ℝ)+(124715384507/68225000000000 : ℝ)*((2809/20000 : ℝ)+(2829/25000 : ℝ))=(5000604981245459/5000000000000000 : ℝ) by norm_num, show 1+(3468463082326711/10000000000000000000 : ℝ)+(288638375394577/2000000000000000000 : ℝ)=(2501227913739824899/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3468463082326711/10000000000000000000 : ℝ) ≤ ((13640325180085893557/13645000000000000000 : ℝ)+2*(124715384507/68225000000000 : ℝ)*(2809/20000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (13640325180085893557/13645000000000000000 : ℝ)+2*(124715384507/68225000000000 : ℝ)*(2809/20000 : ℝ)=(5000854412014473/5000000000000000 : ℝ) by norm_num, show 1+2*(3468463082326711/10000000000000000000 : ℝ)=(5003468463082326711/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13640325180085893557/13645000000000000000 : ℝ)*(X 1 0+X 2 0)+(124715384507/68225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (2829/25000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (13640325180085893557/13645000000000000000 : ℝ)) (alpha := (124715384507/68225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13640325180085893557/13645000000000000000 : ℝ)*(X 0 1+X 2 1)+(124715384507/68225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (2829/25000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (13640325180085893557/13645000000000000000 : ℝ)) (alpha := (124715384507/68225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13640325180085893557/13645000000000000000 : ℝ)*(X 0 2+X 1 2)+(124715384507/68225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (2829/25000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (13640325180085893557/13645000000000000000 : ℝ)) (alpha := (124715384507/68225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-272180863/1250000000 : ℝ)*X 0 0+(5393467531/10000000000 : ℝ)*X 0 1+(5265341767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344844479/10000000000 : ℝ)*X 1 0+(-2242440657/10000000000 : ℝ)*X 1 1+(5265341769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344844479/10000000000 : ℝ)*X 2 0+(526534177/1000000000 : ℝ)*X 2 1+(-448488131/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4367779779/10000000000 : ℝ)*X 0 0+(1060680511/2500000000 : ℝ)*X 0 1+(7025821/15625000 : ℝ)*X 0 2+(4367779779/10000000000 : ℝ)*X 1 0+(1060680511/2500000000 : ℝ)*X 1 1+(7025821/15625000 : ℝ)*X 1 2+(4367779779/10000000000 : ℝ)*X 2 0+(1060680511/2500000000 : ℝ)*X 2 1+(7025821/15625000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2177451851/10000000000 : ℝ)*X 0 0+(1316415893/2500000000 : ℝ)*X 0 1+(5393144561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664054579/1250000000 : ℝ)*X 1 0+(-2114637863/10000000000 : ℝ)*X 1 1+(2696572271/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312436629/10000000000 : ℝ)*X 2 0+(215725781/400000000 : ℝ)*X 2 1+(-211463789/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367789557/10000000000 : ℝ)*X 0 0+(280992997/625000000 : ℝ)*X 0 1+(2121680927/5000000000 : ℝ)*X 0 2+(4367789557/10000000000 : ℝ)*X 1 0+(280992997/625000000 : ℝ)*X 1 1+(2121680927/5000000000 : ℝ)*X 1 2+(4367789557/10000000000 : ℝ)*X 2 0+(280992997/625000000 : ℝ)*X 2 1+(2121680927/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (195852214730433670856121111/21320312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (915247091/50000000000000 : ℝ)*(base19) + (341822279/20000000000000 : ℝ)*(base23) + (16219303/25000000000000 : ℝ)*(lower2) + (230866773/100000000000000 : ℝ)*(upper3) + (143603683/100000000000000 : ℝ)*(upper5) + (367032582711407/6250000000000 : ℝ)*(major0) + (367032582711407/6250000000000 : ℝ)*(major1) + (367032582711407/6250000000000 : ℝ)*(major2) + (3902441757878637/50000000000000 : ℝ)*(sp0) + (487808222292541/6250000000000 : ℝ)*(sp1) + (7804931678063443/100000000000000 : ℝ)*(sp2) + (3940081996578131/100000000000000 : ℝ)*(sp3) + (12467854391/25000000000000 : ℝ)*(sp4) + (13478403033/50000000000000 : ℝ)*(sp7) + (3940108953384197/100000000000000 : ℝ)*(f.failure) + (7804933387174837/100000000000000 : ℝ)*(f.sum) + (9849222769059/13645000000000000000000000000 : ℝ)*base66 + (32783187211057801/85281250000000000000000000000000 : ℝ)*base68 + (2042359590766432801/85281250000000000000000000000000 : ℝ)*base70 + (662456994611660949/85281250000000000000000000000000 : ℝ)*base71 + (5041999299939/3411250000000000000000000000 : ℝ)*base73 + (77342109033870301/85281250000000000000000000000000 : ℝ)*base76 + (752634840445504699/85281250000000000000000000000000 : ℝ)*base77 + (2095401043674557801/85281250000000000000000000000000 : ℝ)*base80 + (66679401816819/13645000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (83706671/10000000000000000000000 : ℝ)*base89 + (83706671/10000000000000000000000 : ℝ)*base91 + (83706671/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1315450881784688588088713859/341125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (780828441/100000000000000 : ℝ)*(base19) + (159538387/20000000000000 : ℝ)*(base23) + (2494357/4000000000000 : ℝ)*(upper3) + (8837967/50000000000000 : ℝ)*(lower4) + (22864973/25000000000000 : ℝ)*(upper5) + (5902146826038571/100000000000000 : ℝ)*(major0) + (5902146826038571/100000000000000 : ℝ)*(major1) + (5902146826038571/100000000000000 : ℝ)*(major2) + (22100715021/100000000000000 : ℝ)*(sp1) + (10068492833/50000000000000 : ℝ)*(sp2) + (784430763793959/10000000000000 : ℝ)*(sp4) + (245133898637379/3125000000000 : ℝ)*(sp5) + (784428670326199/10000000000000 : ℝ)*(sp6) + (395998588559709/10000000000000 : ℝ)*(sp7) + (395998588559709/10000000000000 : ℝ)*(f.failure) + (784430763793959/10000000000000 : ℝ)*(f.sum) + (15847366518047/3411250000000000000000000000 : ℝ)*base65 + (5925543151161787047/1364500000000000000000000000000000 : ℝ)*base67 + (14002701324156787047/1364500000000000000000000000000000 : ℝ)*base69 + (14451493240499287047/1364500000000000000000000000000000 : ℝ)*base71 + (17529325440733/13645000000000000000000000000 : ℝ)*base73 + (7050470756649287047/1364500000000000000000000000000000 : ℝ)*base75 + (12476666350698787047/1364500000000000000000000000000000 : ℝ)*base77 + (15757123362643212953/1364500000000000000000000000000000 : ℝ)*base80 + (3462924503069/6822500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2088887/1000000000000000000000 : ℝ)*base89 + (2088887/1000000000000000000000 : ℝ)*base91 + (2088887/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1120_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2829/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1120_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1120_s8_0 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2177455759/10000000000 : ℝ)*x 0 + (674173687/1250000000 : ℝ)*x 1 + (2632706891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177455759/10000000000 : ℝ)^8313 ≤ (661451483993/5000000000000 : ℝ)^6265 := by
    have hnat : (2177455759 : ℕ)^8313*5000000000000^6265 ≤ 661451483993^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177455759 10000000000 661451483993 5000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674173687/1250000000 : ℝ)^8313 ≤ (22038327196933/50000000000000 : ℝ)^6265 := by
    have hnat : (674173687 : ℕ)^8313*50000000000000^6265 ≤ 22038327196933^6265*1250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674173687 1250000000 22038327196933 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632706891/5000000000 : ℝ)^8313 ≤ (10673578977013/25000000000000 : ℝ)^6265 := by
    have hnat : (2632706891 : ℕ)^8313*25000000000000^6265 ≤ 10673578977013^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632706891 5000000000 10673578977013 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2177455759/10000000000 : ℝ), (674173687/1250000000 : ℝ), (2632706891/5000000000 : ℝ)] ![(661451483993/5000000000000 : ℝ), (22038327196933/50000000000000 : ℝ), (10673578977013/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2177455759/10000000000 : ℝ)|^8313 ≤ (661451483993/5000000000000 : ℝ)^6265
        have hw : |(-2177455759/10000000000 : ℝ)|=(2177455759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674173687/1250000000 : ℝ)|^8313 ≤ (22038327196933/50000000000000 : ℝ)^6265
        have hw : |(674173687/1250000000 : ℝ)|=(674173687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632706891/5000000000 : ℝ)|^8313 ≤ (10673578977013/25000000000000 : ℝ)^6265
        have hw : |(2632706891/5000000000 : ℝ)|=(2632706891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s8_1 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (21379297/40000000 : ℝ)*x 0 + (-89694893/400000000 : ℝ)*x 1 + (5265413791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21379297/40000000 : ℝ)^8313 ≤ (43550796762639/100000000000000 : ℝ)^6265 := by
    have hnat : (21379297 : ℕ)^8313*100000000000000^6265 ≤ 43550796762639^6265*40000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21379297 40000000 43550796762639 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89694893/400000000 : ℝ)^8313 ≤ (13754887215797/100000000000000 : ℝ)^6265 := by
    have hnat : (89694893 : ℕ)^8313*100000000000000^6265 ≤ 13754887215797^6265*400000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89694893 400000000 13754887215797 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265413791/10000000000 : ℝ)^8313 ≤ (42694316004883/100000000000000 : ℝ)^6265 := by
    have hnat : (5265413791 : ℕ)^8313*100000000000000^6265 ≤ 42694316004883^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265413791 10000000000 42694316004883 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21379297/40000000 : ℝ), (-89694893/400000000 : ℝ), (5265413791/10000000000 : ℝ)] ![(43550796762639/100000000000000 : ℝ), (13754887215797/100000000000000 : ℝ), (42694316004883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21379297/40000000 : ℝ)|^8313 ≤ (43550796762639/100000000000000 : ℝ)^6265
        have hw : |(21379297/40000000 : ℝ)|=(21379297/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89694893/400000000 : ℝ)|^8313 ≤ (13754887215797/100000000000000 : ℝ)^6265
        have hw : |(-89694893/400000000 : ℝ)|=(89694893/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265413791/10000000000 : ℝ)|^8313 ≤ (42694316004883/100000000000000 : ℝ)^6265
        have hw : |(5265413791/10000000000 : ℝ)|=(5265413791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s8_2 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344824287/10000000000 : ℝ)*x 0 + (2632706877/5000000000 : ℝ)*x 1 + (-1121186163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344824287/10000000000 : ℝ)^8313 ≤ (43550797162677/100000000000000 : ℝ)^6265 := by
    have hnat : (5344824287 : ℕ)^8313*100000000000000^6265 ≤ 43550797162677^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344824287 10000000000 43550797162677 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632706877/5000000000 : ℝ)^8313 ≤ (21347157803399/50000000000000 : ℝ)^6265 := by
    have hnat : (2632706877 : ℕ)^8313*50000000000000^6265 ≤ 21347157803399^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632706877 5000000000 21347157803399 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121186163/5000000000 : ℝ)^8313 ≤ (13754887223937/100000000000000 : ℝ)^6265 := by
    have hnat : (1121186163 : ℕ)^8313*100000000000000^6265 ≤ 13754887223937^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121186163 5000000000 13754887223937 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344824287/10000000000 : ℝ), (2632706877/5000000000 : ℝ), (-1121186163/5000000000 : ℝ)] ![(43550797162677/100000000000000 : ℝ), (21347157803399/50000000000000 : ℝ), (13754887223937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344824287/10000000000 : ℝ)|^8313 ≤ (43550797162677/100000000000000 : ℝ)^6265
        have hw : |(5344824287/10000000000 : ℝ)|=(5344824287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632706877/5000000000 : ℝ)|^8313 ≤ (21347157803399/50000000000000 : ℝ)^6265
        have hw : |(2632706877/5000000000 : ℝ)|=(2632706877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1121186163/5000000000 : ℝ)|^8313 ≤ (13754887223937/100000000000000 : ℝ)^6265
        have hw : |(-1121186163/5000000000 : ℝ)|=(1121186163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s8_3 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183891791/5000000000 : ℝ)*x 0 + (4242870181/10000000000 : ℝ)*x 1 + (2248188161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183891791/5000000000 : ℝ)^8313 ≤ (33316863179017/100000000000000 : ℝ)^6265 := by
    have hnat : (2183891791 : ℕ)^8313*100000000000000^6265 ≤ 33316863179017^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183891791 5000000000 33316863179017 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242870181/10000000000 : ℝ)^8313 ≤ (16029257745737/50000000000000 : ℝ)^6265 := by
    have hnat : (4242870181 : ℕ)^8313*50000000000000^6265 ≤ 16029257745737^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242870181 10000000000 16029257745737 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248188161/5000000000 : ℝ)^8313 ≤ (34624621315897/100000000000000 : ℝ)^6265 := by
    have hnat : (2248188161 : ℕ)^8313*100000000000000^6265 ≤ 34624621315897^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248188161 5000000000 34624621315897 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183891791/5000000000 : ℝ), (4242870181/10000000000 : ℝ), (2248188161/5000000000 : ℝ)] ![(33316863179017/100000000000000 : ℝ), (16029257745737/50000000000000 : ℝ), (34624621315897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183891791/5000000000 : ℝ)|^8313 ≤ (33316863179017/100000000000000 : ℝ)^6265
        have hw : |(2183891791/5000000000 : ℝ)|=(2183891791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242870181/10000000000 : ℝ)|^8313 ≤ (16029257745737/50000000000000 : ℝ)^6265
        have hw : |(4242870181/10000000000 : ℝ)|=(4242870181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248188161/5000000000 : ℝ)|^8313 ≤ (34624621315897/100000000000000 : ℝ)^6265
        have hw : |(2248188161/5000000000 : ℝ)|=(2248188161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s8_4 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-272182579/1250000000 : ℝ)*x 0 + (52657351/100000000 : ℝ)*x 1 + (2696533531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272182579/1250000000 : ℝ)^8313 ≤ (13229068963519/100000000000000 : ℝ)^6265 := by
    have hnat : (272182579 : ℕ)^8313*100000000000000^6265 ≤ 13229068963519^6265*1250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272182579 1250000000 13229068963519 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52657351/100000000 : ℝ)^8313 ≤ (4269777302161/10000000000000 : ℝ)^6265 := by
    have hnat : (52657351 : ℕ)^8313*10000000000000^6265 ≤ 4269777302161^6265*100000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52657351 100000000 4269777302161 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696533531/5000000000 : ℝ)^8313 ≤ (44073158001771/100000000000000 : ℝ)^6265 := by
    have hnat : (2696533531 : ℕ)^8313*100000000000000^6265 ≤ 44073158001771^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696533531 5000000000 44073158001771 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272182579/1250000000 : ℝ), (52657351/100000000 : ℝ), (2696533531/5000000000 : ℝ)] ![(13229068963519/100000000000000 : ℝ), (4269777302161/10000000000000 : ℝ), (44073158001771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272182579/1250000000 : ℝ)|^8313 ≤ (13229068963519/100000000000000 : ℝ)^6265
        have hw : |(-272182579/1250000000 : ℝ)|=(272182579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52657351/100000000 : ℝ)|^8313 ≤ (4269777302161/10000000000000 : ℝ)^6265
        have hw : |(52657351/100000000 : ℝ)|=(52657351/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696533531/5000000000 : ℝ)|^8313 ≤ (44073158001771/100000000000000 : ℝ)^6265
        have hw : |(2696533531/5000000000 : ℝ)|=(2696533531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s8_5 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312453919/10000000000 : ℝ)*x 0 + (-2114718783/10000000000 : ℝ)*x 1 + (1078613551/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312453919/10000000000 : ℝ)^8313 ≤ (540014512859/1250000000000 : ℝ)^6265 := by
    have hnat : (5312453919 : ℕ)^8313*1250000000000^6265 ≤ 540014512859^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312453919 10000000000 540014512859 1250000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114718783/10000000000 : ℝ)^8313 ≤ (1590709180661/12500000000000 : ℝ)^6265 := by
    have hnat : (2114718783 : ℕ)^8313*12500000000000^6265 ≤ 1590709180661^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114718783 10000000000 1590709180661 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078613551/2000000000 : ℝ)^8313 ≤ (44073165516413/100000000000000 : ℝ)^6265 := by
    have hnat : (1078613551 : ℕ)^8313*100000000000000^6265 ≤ 44073165516413^6265*2000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078613551 2000000000 44073165516413 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312453919/10000000000 : ℝ), (-2114718783/10000000000 : ℝ), (1078613551/2000000000 : ℝ)] ![(540014512859/1250000000000 : ℝ), (1590709180661/12500000000000 : ℝ), (44073165516413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312453919/10000000000 : ℝ)|^8313 ≤ (540014512859/1250000000000 : ℝ)^6265
        have hw : |(5312453919/10000000000 : ℝ)|=(5312453919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2114718783/10000000000 : ℝ)|^8313 ≤ (1590709180661/12500000000000 : ℝ)^6265
        have hw : |(-2114718783/10000000000 : ℝ)|=(2114718783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078613551/2000000000 : ℝ)|^8313 ≤ (44073165516413/100000000000000 : ℝ)^6265
        have hw : |(1078613551/2000000000 : ℝ)|=(1078613551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s8_6 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312454581/10000000000 : ℝ)*x 0 + (5393067059/10000000000 : ℝ)*x 1 + (-1057359417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312454581/10000000000 : ℝ)^8313 ≤ (8640233634391/20000000000000 : ℝ)^6265 := by
    have hnat : (5312454581 : ℕ)^8313*20000000000000^6265 ≤ 8640233634391^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312454581 10000000000 8640233634391 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393067059/10000000000 : ℝ)^8313 ≤ (1101828949231/2500000000000 : ℝ)^6265 := by
    have hnat : (5393067059 : ℕ)^8313*2500000000000^6265 ≤ 1101828949231^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393067059 10000000000 1101828949231 2500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057359417/5000000000 : ℝ)^8313 ≤ (6362836926257/50000000000000 : ℝ)^6265 := by
    have hnat : (1057359417 : ℕ)^8313*50000000000000^6265 ≤ 6362836926257^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057359417 5000000000 6362836926257 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312454581/10000000000 : ℝ), (5393067059/10000000000 : ℝ), (-1057359417/5000000000 : ℝ)] ![(8640233634391/20000000000000 : ℝ), (1101828949231/2500000000000 : ℝ), (6362836926257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312454581/10000000000 : ℝ)|^8313 ≤ (8640233634391/20000000000000 : ℝ)^6265
        have hw : |(5312454581/10000000000 : ℝ)|=(5312454581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393067059/10000000000 : ℝ)|^8313 ≤ (1101828949231/2500000000000 : ℝ)^6265
        have hw : |(5393067059/10000000000 : ℝ)|=(5393067059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1057359417/5000000000 : ℝ)|^8313 ≤ (6362836926257/50000000000000 : ℝ)^6265
        have hw : |(-1057359417/5000000000 : ℝ)|=(1057359417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s8_7 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136493537/312500000 : ℝ)*x 0 + (561967549/1250000000 : ℝ)*x 1 + (2121754283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136493537/312500000 : ℝ)^8313 ≤ (4164620045567/12500000000000 : ℝ)^6265 := by
    have hnat : (136493537 : ℕ)^8313*12500000000000^6265 ≤ 4164620045567^6265*312500000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136493537 312500000 4164620045567 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561967549/1250000000 : ℝ)^8313 ≤ (17309061817653/50000000000000 : ℝ)^6265 := by
    have hnat : (561967549 : ℕ)^8313*50000000000000^6265 ≤ 17309061817653^6265*1250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561967549 1250000000 17309061817653 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121754283/5000000000 : ℝ)^8313 ≤ (16032457994419/50000000000000 : ℝ)^6265 := by
    have hnat : (2121754283 : ℕ)^8313*50000000000000^6265 ≤ 16032457994419^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121754283 5000000000 16032457994419 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136493537/312500000 : ℝ), (561967549/1250000000 : ℝ), (2121754283/5000000000 : ℝ)] ![(4164620045567/12500000000000 : ℝ), (17309061817653/50000000000000 : ℝ), (16032457994419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136493537/312500000 : ℝ)|^8313 ≤ (4164620045567/12500000000000 : ℝ)^6265
        have hw : |(136493537/312500000 : ℝ)|=(136493537/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561967549/1250000000 : ℝ)|^8313 ≤ (17309061817653/50000000000000 : ℝ)^6265
        have hw : |(561967549/1250000000 : ℝ)|=(561967549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121754283/5000000000 : ℝ)|^8313 ≤ (16032457994419/50000000000000 : ℝ)^6265
        have hw : |(2121754283/5000000000 : ℝ)|=(2121754283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1120_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (453/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3509/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14037/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11323/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14037/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11323/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14037/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11323/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14037/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11323/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14037/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11323/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14037/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11323/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11323/100000 : ℝ) ^ (1039/256 : ℝ) ≤ (14468186100006217/100000000000000000000 : ℝ) := by
    have hpowers : (11323/100000 : ℝ)^1039 ≤ (14468186100006217/100000000000000000000 : ℝ)^256 := by
      have hnat : (11323 : ℕ)^1039*100000000000000000000^256 ≤ 14468186100006217^256*100000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11323 100000 14468186100006217 100000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11323/100000 : ℝ)) (X := (14468186100006217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14037/100000 : ℝ) ^ (1039/256 : ℝ) ≤ (34604517900185607/100000000000000000000 : ℝ) := by
    have hpowers : (14037/100000 : ℝ)^1039 ≤ (34604517900185607/100000000000000000000 : ℝ)^256 := by
      have hnat : (14037 : ℕ)^1039*100000000000000000000^256 ≤ 34604517900185607^256*100000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14037 100000 34604517900185607 100000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14037/100000 : ℝ)) (X := (34604517900185607/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014468186100006217/50000000000000000000 : ℝ) ≤ (5000356443875383/5000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (50014468186100006217/50000000000000000000 : ℝ)^256 ≤ (5000356443875383/5000000000000000 : ℝ)^1039 := by
      have hnat : (50014468186100006217 : ℕ)^256*5000000000000000^1039 ≤ 5000356443875383^1039*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014468186100006217 50000000000000000000 5000356443875383 5000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000356443875383/5000000000000000 : ℝ)) (X := (50014468186100006217/50000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253067044000011989/6250000000000000000 : ℝ) ≤ (2500302220643887/2500000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (6253067044000011989/6250000000000000000 : ℝ)^256 ≤ (2500302220643887/2500000000000000 : ℝ)^1039 := by
      have hnat : (6253067044000011989 : ℕ)^256*2500000000000000^1039 ≤ 2500302220643887^1039*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253067044000011989 6250000000000000000 2500302220643887 2500000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500302220643887/2500000000000000 : ℝ)) (X := (6253067044000011989/6250000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034604517900185607/50000000000000000000 : ℝ) ≤ (1000170487740033/1000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (50034604517900185607/50000000000000000000 : ℝ)^256 ≤ (1000170487740033/1000000000000000 : ℝ)^1039 := by
      have hnat : (50034604517900185607 : ℕ)^256*1000000000000000^1039 ≤ 1000170487740033^1039*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034604517900185607 50000000000000000000 1000170487740033 1000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000170487740033/1000000000000000 : ℝ)) (X := (50034604517900185607/50000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14468186100006217/100000000000000000000 : ℝ) ≤ ((3391337809819195719/3392500000000000000 : ℝ)+2*(247997412391/135700000000000 : ℝ)*(11323/100000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (3391337809819195719/3392500000000000000 : ℝ)+2*(247997412391/135700000000000 : ℝ)*(11323/100000 : ℝ)=(5000356443875383/5000000000000000 : ℝ) by norm_num, show 1+2*(14468186100006217/100000000000000000000 : ℝ)=(50014468186100006217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34604517900185607/100000000000000000000 : ℝ)+(14468186100006217/100000000000000000000 : ℝ) ≤ ((3391337809819195719/3392500000000000000 : ℝ)+(247997412391/135700000000000 : ℝ)*((14037/100000 : ℝ)+(11323/100000 : ℝ)))^(1039/256 : ℝ) := by
    rw [show (3391337809819195719/3392500000000000000 : ℝ)+(247997412391/135700000000000 : ℝ)*((14037/100000 : ℝ)+(11323/100000 : ℝ))=(2500302220643887/2500000000000000 : ℝ) by norm_num, show 1+(34604517900185607/100000000000000000000 : ℝ)+(14468186100006217/100000000000000000000 : ℝ)=(6253067044000011989/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34604517900185607/100000000000000000000 : ℝ) ≤ ((3391337809819195719/3392500000000000000 : ℝ)+2*(247997412391/135700000000000 : ℝ)*(14037/100000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (3391337809819195719/3392500000000000000 : ℝ)+2*(247997412391/135700000000000 : ℝ)*(14037/100000 : ℝ)=(1000170487740033/1000000000000000 : ℝ) by norm_num, show 1+2*(34604517900185607/100000000000000000000 : ℝ)=(50034604517900185607/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3391337809819195719/3392500000000000000 : ℝ)*(X 1 0+X 2 0)+(247997412391/135700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (14037/100000 : ℝ)) (c := (3391337809819195719/3392500000000000000 : ℝ)) (alpha := (247997412391/135700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3391337809819195719/3392500000000000000 : ℝ)*(X 0 1+X 2 1)+(247997412391/135700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (14037/100000 : ℝ)) (c := (3391337809819195719/3392500000000000000 : ℝ)) (alpha := (247997412391/135700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3391337809819195719/3392500000000000000 : ℝ)*(X 0 2+X 1 2)+(247997412391/135700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (14037/100000 : ℝ)) (c := (3391337809819195719/3392500000000000000 : ℝ)) (alpha := (247997412391/135700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2177455759/10000000000 : ℝ)*X 0 0+(674173687/1250000000 : ℝ)*X 0 1+(2632706891/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((21379297/40000000 : ℝ)*X 1 0+(-89694893/400000000 : ℝ)*X 1 1+(5265413791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344824287/10000000000 : ℝ)*X 2 0+(2632706877/5000000000 : ℝ)*X 2 1+(-1121186163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183891791/5000000000 : ℝ)*X 0 0+(4242870181/10000000000 : ℝ)*X 0 1+(2248188161/5000000000 : ℝ)*X 0 2+(2183891791/5000000000 : ℝ)*X 1 0+(4242870181/10000000000 : ℝ)*X 1 1+(2248188161/5000000000 : ℝ)*X 1 2+(2183891791/5000000000 : ℝ)*X 2 0+(4242870181/10000000000 : ℝ)*X 2 1+(2248188161/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-272182579/1250000000 : ℝ)*X 0 0+(52657351/100000000 : ℝ)*X 0 1+(2696533531/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312453919/10000000000 : ℝ)*X 1 0+(-2114718783/10000000000 : ℝ)*X 1 1+(1078613551/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312454581/10000000000 : ℝ)*X 2 0+(5393067059/10000000000 : ℝ)*X 2 1+(-1057359417/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136493537/312500000 : ℝ)*X 0 0+(561967549/1250000000 : ℝ)*X 0 1+(2121754283/5000000000 : ℝ)*X 0 2+(136493537/312500000 : ℝ)*X 1 0+(561967549/1250000000 : ℝ)*X 1 1+(2121754283/5000000000 : ℝ)*X 1 2+(136493537/312500000 : ℝ)*X 2 0+(561967549/1250000000 : ℝ)*X 2 1+(2121754283/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (420400164257219257945423569/84812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9263953/1000000000000 : ℝ)*(base19) + (473131397/50000000000000 : ℝ)*(base23) + (2286637/12500000000000 : ℝ)*(lower2) + (112705419/100000000000000 : ℝ)*(upper3) + (12087239/12500000000000 : ℝ)*(upper5) + (5879368877701717/100000000000000 : ℝ)*(major0) + (5879368877701717/100000000000000 : ℝ)*(major1) + (5879368877701717/100000000000000 : ℝ)*(major2) + (7814008257928711/100000000000000 : ℝ)*(sp0) + (1953508353222153/25000000000000 : ℝ)*(sp1) + (3907016696510559/50000000000000 : ℝ)*(sp2) + (1972345006074391/50000000000000 : ℝ)*(sp3) + (13040677601/50000000000000 : ℝ)*(sp4) + (1654842931/12500000000000 : ℝ)*(sp7) + (3944703250892229/100000000000000 : ℝ)*(f.failure) + (7814034339283913/100000000000000 : ℝ)*(f.sum) + (6534689801051/848125000000000000000000000 : ℝ)*base66 + (6675863017990475477/339250000000000000000000000000000 : ℝ)*base68 + (2781760141637475477/339250000000000000000000000000000 : ℝ)*base70 + (817173453113975477/339250000000000000000000000000000 : ℝ)*base72 + (17047132005183/6785000000000000000000000000 : ℝ)*base74 + (1672525673347024523/339250000000000000000000000000000 : ℝ)*base75 + (4828415198654475477/339250000000000000000000000000000 : ℝ)*base78 + (3611230202093475477/339250000000000000000000000000000 : ℝ)*base80 + (32841096548293/6785000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2779247/10000000000000000000000 : ℝ)*base89 + (2779247/10000000000000000000000 : ℝ)*base91 + (2779247/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19178621572696938412293/1696250000000000000000000000 : ℝ) := by norm_num
    linear_combination (948218579/100000000000000 : ℝ)*(base19) + (529219427/25000000000000 : ℝ)*(base23) + (81904073/12500000000000 : ℝ)*(lower1) + (162924039/50000000000000 : ℝ)*(upper3) + (22057499/50000000000000 : ℝ)*(lower4) + (29945793/100000000000000 : ℝ)*(upper5) + (5909011737480591/100000000000000 : ℝ)*(major0) + (5909011737480591/100000000000000 : ℝ)*(major1) + (5909011737480591/100000000000000 : ℝ)*(major2) + (438934717/2500000000000 : ℝ)*(sp2) + (490839454336673/6250000000000 : ℝ)*(sp4) + (7853430321168189/100000000000000 : ℝ)*(sp5) + (7853411595120379/100000000000000 : ℝ)*(sp6) + (123893494646613/3125000000000 : ℝ)*(sp7) + (123893494646613/3125000000000 : ℝ)*(f.failure) + (490839454336673/6250000000000 : ℝ)*(f.sum) + (5140889359799/6785000000000000000000000000 : ℝ)*base66 + (30486878253706185071/339250000000000000000000000000000 : ℝ)*base68 + (2793001232293814929/339250000000000000000000000000000 : ℝ)*base69 + (64401571079803935071/339250000000000000000000000000000 : ℝ)*base72 + (611979824339/1696250000000000000000000000 : ℝ)*base73 + (3950450962993064929/339250000000000000000000000000000 : ℝ)*base75 + (1137109745922935071/339250000000000000000000000000000 : ℝ)*base78 + (6359999463214564929/339250000000000000000000000000000 : ℝ)*base79 + (33254293074431/6785000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1130841/312500000000000000000 : ℝ)*base90 + (1130841/312500000000000000000 : ℝ)*base92 + (1130841/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1120_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1120_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1120_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1120_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1120_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1120_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1120_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
