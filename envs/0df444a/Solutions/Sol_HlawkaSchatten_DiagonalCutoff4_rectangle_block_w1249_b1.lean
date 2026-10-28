-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1249_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:23:01.982204+00:00
-- url     : https://prove2.me/submissions/1dba3e9a-4a5d-4211-887d-47d8e85aabe7

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
theorem support_rectangle_w1249_s3_0 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056977241/5000000000 : ℝ)*x 0 + (677381057/1250000000 : ℝ)*x 1 + (1048231029/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056977241/5000000000 : ℝ)^4221 ≤ (1606325618061/12500000000000 : ℝ)^3197 := by
    have hnat : (1056977241 : ℕ)^4221*12500000000000^3197 ≤ 1606325618061^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056977241 5000000000 1606325618061 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677381057/1250000000 : ℝ)^4221 ≤ (44534697569637/100000000000000 : ℝ)^3197 := by
    have hnat : (677381057 : ℕ)^4221*100000000000000^3197 ≤ 44534697569637^3197*1250000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677381057 1250000000 44534697569637 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048231029/2000000000 : ℝ)^4221 ≤ (42614697472733/100000000000000 : ℝ)^3197 := by
    have hnat : (1048231029 : ℕ)^4221*100000000000000^3197 ≤ 42614697472733^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048231029 2000000000 42614697472733 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056977241/5000000000 : ℝ), (677381057/1250000000 : ℝ), (1048231029/2000000000 : ℝ)] ![(1606325618061/12500000000000 : ℝ), (44534697569637/100000000000000 : ℝ), (42614697472733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056977241/5000000000 : ℝ)|^4221 ≤ (1606325618061/12500000000000 : ℝ)^3197
        have hw : |(-1056977241/5000000000 : ℝ)|=(1056977241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677381057/1250000000 : ℝ)|^4221 ≤ (44534697569637/100000000000000 : ℝ)^3197
        have hw : |(677381057/1250000000 : ℝ)|=(677381057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048231029/2000000000 : ℝ)|^4221 ≤ (42614697472733/100000000000000 : ℝ)^3197
        have hw : |(1048231029/2000000000 : ℝ)|=(1048231029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s3_1 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675668261/5000000000 : ℝ)*x 0 + (-2204693229/10000000000 : ℝ)*x 1 + (327572203/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675668261/5000000000 : ℝ)^4221 ≤ (1095036656977/2500000000000 : ℝ)^3197 := by
    have hnat : (2675668261 : ℕ)^4221*2500000000000^3197 ≤ 1095036656977^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675668261 5000000000 1095036656977 2500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2204693229/10000000000 : ℝ)^4221 ≤ (1697979391073/12500000000000 : ℝ)^3197 := by
    have hnat : (2204693229 : ℕ)^4221*12500000000000^3197 ≤ 1697979391073^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204693229 10000000000 1697979391073 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327572203/625000000 : ℝ)^4221 ≤ (8522939715689/20000000000000 : ℝ)^3197 := by
    have hnat : (327572203 : ℕ)^4221*20000000000000^3197 ≤ 8522939715689^3197*625000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327572203 625000000 8522939715689 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675668261/5000000000 : ℝ), (-2204693229/10000000000 : ℝ), (327572203/625000000 : ℝ)] ![(1095036656977/2500000000000 : ℝ), (1697979391073/12500000000000 : ℝ), (8522939715689/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675668261/5000000000 : ℝ)|^4221 ≤ (1095036656977/2500000000000 : ℝ)^3197
        have hw : |(2675668261/5000000000 : ℝ)|=(2675668261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2204693229/10000000000 : ℝ)|^4221 ≤ (1697979391073/12500000000000 : ℝ)^3197
        have hw : |(-2204693229/10000000000 : ℝ)|=(2204693229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327572203/625000000 : ℝ)|^4221 ≤ (8522939715689/20000000000000 : ℝ)^3197
        have hw : |(327572203/625000000 : ℝ)|=(327572203/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s3_2 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351336467/10000000000 : ℝ)*x 0 + (2620577851/5000000000 : ℝ)*x 1 + (-2204692703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351336467/10000000000 : ℝ)^4221 ≤ (1368795802647/3125000000000 : ℝ)^3197 := by
    have hnat : (5351336467 : ℕ)^4221*3125000000000^3197 ≤ 1368795802647^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351336467 10000000000 1368795802647 3125000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620577851/5000000000 : ℝ)^4221 ≤ (4261470345217/10000000000000 : ℝ)^3197 := by
    have hnat : (2620577851 : ℕ)^4221*10000000000000^3197 ≤ 4261470345217^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620577851 5000000000 4261470345217 10000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204692703/10000000000 : ℝ)^4221 ≤ (13583830849679/100000000000000 : ℝ)^3197 := by
    have hnat : (2204692703 : ℕ)^4221*100000000000000^3197 ≤ 13583830849679^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204692703 10000000000 13583830849679 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351336467/10000000000 : ℝ), (2620577851/5000000000 : ℝ), (-2204692703/10000000000 : ℝ)] ![(1368795802647/3125000000000 : ℝ), (4261470345217/10000000000000 : ℝ), (13583830849679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351336467/10000000000 : ℝ)|^4221 ≤ (1368795802647/3125000000000 : ℝ)^3197
        have hw : |(5351336467/10000000000 : ℝ)|=(5351336467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620577851/5000000000 : ℝ)|^4221 ≤ (4261470345217/10000000000000 : ℝ)^3197
        have hw : |(2620577851/5000000000 : ℝ)|=(2620577851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2204692703/10000000000 : ℝ)|^4221 ≤ (13583830849679/100000000000000 : ℝ)^3197
        have hw : |(-2204692703/10000000000 : ℝ)|=(2204692703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s3_3 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4348149029/10000000000 : ℝ)*x 0 + (834222301/2000000000 : ℝ)*x 1 + (1133116723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348149029/10000000000 : ℝ)^4221 ≤ (16650344714869/50000000000000 : ℝ)^3197 := by
    have hnat : (4348149029 : ℕ)^4221*50000000000000^3197 ≤ 16650344714869^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348149029 10000000000 16650344714869 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834222301/2000000000 : ℝ)^4221 ≤ (15761166204703/50000000000000 : ℝ)^3197 := by
    have hnat : (834222301 : ℕ)^4221*50000000000000^3197 ≤ 15761166204703^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834222301 2000000000 15761166204703 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133116723/2500000000 : ℝ)^4221 ≤ (35176978149313/100000000000000 : ℝ)^3197 := by
    have hnat : (1133116723 : ℕ)^4221*100000000000000^3197 ≤ 35176978149313^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133116723 2500000000 35176978149313 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348149029/10000000000 : ℝ), (834222301/2000000000 : ℝ), (1133116723/2500000000 : ℝ)] ![(16650344714869/50000000000000 : ℝ), (15761166204703/50000000000000 : ℝ), (35176978149313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348149029/10000000000 : ℝ)|^4221 ≤ (16650344714869/50000000000000 : ℝ)^3197
        have hw : |(4348149029/10000000000 : ℝ)|=(4348149029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834222301/2000000000 : ℝ)|^4221 ≤ (15761166204703/50000000000000 : ℝ)^3197
        have hw : |(834222301/2000000000 : ℝ)|=(834222301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133116723/2500000000 : ℝ)|^4221 ≤ (35176978149313/100000000000000 : ℝ)^3197
        have hw : |(1133116723/2500000000 : ℝ)|=(1133116723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s3_4 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2113968569/10000000000 : ℝ)*x 0 + (2620899561/5000000000 : ℝ)*x 1 + (2709200441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113968569/10000000000 : ℝ)^4221 ≤ (6425359003631/50000000000000 : ℝ)^3197 := by
    have hnat : (2113968569 : ℕ)^4221*50000000000000^3197 ≤ 6425359003631^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113968569 10000000000 6425359003631 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620899561/5000000000 : ℝ)^4221 ≤ (21310805375293/50000000000000 : ℝ)^3197 := by
    have hnat : (2620899561 : ℕ)^4221*50000000000000^3197 ≤ 21310805375293^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620899561 5000000000 21310805375293 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709200441/5000000000 : ℝ)^4221 ≤ (5565958903463/12500000000000 : ℝ)^3197 := by
    have hnat : (2709200441 : ℕ)^4221*12500000000000^3197 ≤ 5565958903463^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709200441 5000000000 5565958903463 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2113968569/10000000000 : ℝ), (2620899561/5000000000 : ℝ), (2709200441/5000000000 : ℝ)] ![(6425359003631/50000000000000 : ℝ), (21310805375293/50000000000000 : ℝ), (5565958903463/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2113968569/10000000000 : ℝ)|^4221 ≤ (6425359003631/50000000000000 : ℝ)^3197
        have hw : |(-2113968569/10000000000 : ℝ)|=(2113968569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620899561/5000000000 : ℝ)|^4221 ≤ (21310805375293/50000000000000 : ℝ)^3197
        have hw : |(2620899561/5000000000 : ℝ)|=(2620899561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709200441/5000000000 : ℝ)|^4221 ≤ (5565958903463/12500000000000 : ℝ)^3197
        have hw : |(2709200441/5000000000 : ℝ)|=(2709200441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s3_5 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652965119/5000000000 : ℝ)*x 0 + (-1013723761/5000000000 : ℝ)*x 1 + (338650069/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652965119/5000000000 : ℝ)^4221 ≤ (43311435490103/100000000000000 : ℝ)^3197 := by
    have hnat : (2652965119 : ℕ)^4221*100000000000000^3197 ≤ 43311435490103^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652965119 5000000000 43311435490103 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1013723761/5000000000 : ℝ)^4221 ≤ (1520111356727/12500000000000 : ℝ)^3197 := by
    have hnat : (1013723761 : ℕ)^4221*12500000000000^3197 ≤ 1520111356727^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013723761 5000000000 1520111356727 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338650069/625000000 : ℝ)^4221 ≤ (22263836818207/50000000000000 : ℝ)^3197 := by
    have hnat : (338650069 : ℕ)^4221*50000000000000^3197 ≤ 22263836818207^3197*625000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338650069 625000000 22263836818207 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652965119/5000000000 : ℝ), (-1013723761/5000000000 : ℝ), (338650069/625000000 : ℝ)] ![(43311435490103/100000000000000 : ℝ), (1520111356727/12500000000000 : ℝ), (22263836818207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652965119/5000000000 : ℝ)|^4221 ≤ (43311435490103/100000000000000 : ℝ)^3197
        have hw : |(2652965119/5000000000 : ℝ)|=(2652965119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1013723761/5000000000 : ℝ)|^4221 ≤ (1520111356727/12500000000000 : ℝ)^3197
        have hw : |(-1013723761/5000000000 : ℝ)|=(1013723761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338650069/625000000 : ℝ)|^4221 ≤ (22263836818207/50000000000000 : ℝ)^3197
        have hw : |(338650069/625000000 : ℝ)|=(338650069/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s3_6 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305930333/10000000000 : ℝ)*x 0 + (1083680203/2000000000 : ℝ)*x 1 + (-506861879/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305930333/10000000000 : ℝ)^4221 ≤ (10827859128489/25000000000000 : ℝ)^3197 := by
    have hnat : (5305930333 : ℕ)^4221*25000000000000^3197 ≤ 10827859128489^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305930333 10000000000 10827859128489 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083680203/2000000000 : ℝ)^4221 ≤ (1113191816769/2500000000000 : ℝ)^3197 := by
    have hnat : (1083680203 : ℕ)^4221*2500000000000^3197 ≤ 1113191816769^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083680203 2000000000 1113191816769 2500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506861879/2500000000 : ℝ)^4221 ≤ (121608908063/1000000000000 : ℝ)^3197 := by
    have hnat : (506861879 : ℕ)^4221*1000000000000^3197 ≤ 121608908063^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506861879 2500000000 121608908063 1000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305930333/10000000000 : ℝ), (1083680203/2000000000 : ℝ), (-506861879/2500000000 : ℝ)] ![(10827859128489/25000000000000 : ℝ), (1113191816769/2500000000000 : ℝ), (121608908063/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305930333/10000000000 : ℝ)|^4221 ≤ (10827859128489/25000000000000 : ℝ)^3197
        have hw : |(5305930333/10000000000 : ℝ)|=(5305930333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083680203/2000000000 : ℝ)|^4221 ≤ (1113191816769/2500000000000 : ℝ)^3197
        have hw : |(1083680203/2000000000 : ℝ)|=(1083680203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-506861879/2500000000 : ℝ)|^4221 ≤ (121608908063/1000000000000 : ℝ)^3197
        have hw : |(-506861879/2500000000 : ℝ)|=(506861879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s3_7 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4348177169/10000000000 : ℝ)*x 0 + (2265579739/5000000000 : ℝ)*x 1 + (4172425533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348177169/10000000000 : ℝ)^4221 ≤ (3330097397153/10000000000000 : ℝ)^3197 := by
    have hnat : (4348177169 : ℕ)^4221*10000000000000^3197 ≤ 3330097397153^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348177169 10000000000 3330097397153 10000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265579739/5000000000 : ℝ)^4221 ≤ (35163581701053/100000000000000 : ℝ)^3197 := by
    have hnat : (2265579739 : ℕ)^4221*100000000000000^3197 ≤ 35163581701053^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265579739 5000000000 35163581701053 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172425533/10000000000 : ℝ)^4221 ≤ (6307088862851/20000000000000 : ℝ)^3197 := by
    have hnat : (4172425533 : ℕ)^4221*20000000000000^3197 ≤ 6307088862851^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172425533 10000000000 6307088862851 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348177169/10000000000 : ℝ), (2265579739/5000000000 : ℝ), (4172425533/10000000000 : ℝ)] ![(3330097397153/10000000000000 : ℝ), (35163581701053/100000000000000 : ℝ), (6307088862851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348177169/10000000000 : ℝ)|^4221 ≤ (3330097397153/10000000000000 : ℝ)^3197
        have hw : |(4348177169/10000000000 : ℝ)|=(4348177169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2265579739/5000000000 : ℝ)|^4221 ≤ (35163581701053/100000000000000 : ℝ)^3197
        have hw : |(2265579739/5000000000 : ℝ)|=(2265579739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172425533/10000000000 : ℝ)|^4221 ≤ (6307088862851/20000000000000 : ℝ)^3197
        have hw : |(4172425533/10000000000 : ℝ)|=(4172425533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1249_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3241/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1191/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10929/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7347/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3241/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1191/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3241/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1191/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3241/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1191/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3241/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1191/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3241/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1191/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3241/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1191/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1191/12500 : ℝ) ^ (8441/2048 : ℝ) ≤ (3096292329679231/50000000000000000000 : ℝ) := by
    have hpowers : (1191/12500 : ℝ)^8441 ≤ (3096292329679231/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1191 : ℕ)^8441*50000000000000000000^2048 ≤ 3096292329679231^2048*12500^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1191 12500 3096292329679231 50000000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1191/12500 : ℝ)) (X := (3096292329679231/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3241/20000 : ℝ) ^ (8441/2048 : ℝ) ≤ (215905497385589/390625000000000000 : ℝ) := by
    have hpowers : (3241/20000 : ℝ)^8441 ≤ (215905497385589/390625000000000000 : ℝ)^2048 := by
      have hnat : (3241 : ℕ)^8441*390625000000000000^2048 ≤ 215905497385589^2048*20000^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3241 20000 215905497385589 390625000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3241/20000 : ℝ)) (X := (215905497385589/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003096292329679231/25000000000000000000 : ℝ) ≤ (2500075120356633/2500000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (25003096292329679231/25000000000000000000 : ℝ)^2048 ≤ (2500075120356633/2500000000000000 : ℝ)^8441 := by
      have hnat : (25003096292329679231 : ℕ)^2048*2500000000000000^8441 ≤ 2500075120356633^8441*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003096292329679231 25000000000000000000 2500075120356633 2500000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500075120356633/2500000000000000 : ℝ)) (X := (25003096292329679231/25000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50030732195995034623/50000000000000000000 : ℝ) ≤ (10001490934557441/10000000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (50030732195995034623/50000000000000000000 : ℝ)^2048 ≤ (10001490934557441/10000000000000000 : ℝ)^8441 := by
      have hnat : (50030732195995034623 : ℕ)^2048*10000000000000000^8441 ≤ 10001490934557441^8441*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030732195995034623 50000000000000000000 10001490934557441 10000000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001490934557441/10000000000000000 : ℝ)) (X := (50030732195995034623/50000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (195528405497385589/195312500000000000 : ℝ) ≤ (200053627753767/200000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (195528405497385589/195312500000000000 : ℝ)^2048 ≤ (200053627753767/200000000000000 : ℝ)^8441 := by
      have hnat : (195528405497385589 : ℕ)^2048*200000000000000^8441 ≤ 200053627753767^8441*195312500000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195528405497385589 195312500000000000 200053627753767 200000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200053627753767/200000000000000 : ℝ)) (X := (195528405497385589/195312500000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3096292329679231/50000000000000000000 : ℝ) ≤ ((3337466051981117613/3338500000000000000 : ℝ)+2*(1190453130909/667700000000000 : ℝ)*(1191/12500 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (3337466051981117613/3338500000000000000 : ℝ)+2*(1190453130909/667700000000000 : ℝ)*(1191/12500 : ℝ)=(2500075120356633/2500000000000000 : ℝ) by norm_num, show 1+2*(3096292329679231/50000000000000000000 : ℝ)=(25003096292329679231/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(215905497385589/390625000000000000 : ℝ)+(3096292329679231/50000000000000000000 : ℝ) ≤ ((3337466051981117613/3338500000000000000 : ℝ)+(1190453130909/667700000000000 : ℝ)*((3241/20000 : ℝ)+(1191/12500 : ℝ)))^(8441/2048 : ℝ) := by
    rw [show (3337466051981117613/3338500000000000000 : ℝ)+(1190453130909/667700000000000 : ℝ)*((3241/20000 : ℝ)+(1191/12500 : ℝ))=(10001490934557441/10000000000000000 : ℝ) by norm_num, show 1+(215905497385589/390625000000000000 : ℝ)+(3096292329679231/50000000000000000000 : ℝ)=(50030732195995034623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(215905497385589/390625000000000000 : ℝ) ≤ ((3337466051981117613/3338500000000000000 : ℝ)+2*(1190453130909/667700000000000 : ℝ)*(3241/20000 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (3337466051981117613/3338500000000000000 : ℝ)+2*(1190453130909/667700000000000 : ℝ)*(3241/20000 : ℝ)=(200053627753767/200000000000000 : ℝ) by norm_num, show 1+2*(215905497385589/390625000000000000 : ℝ)=(195528405497385589/195312500000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3337466051981117613/3338500000000000000 : ℝ)*(X 1 0+X 2 0)+(1190453130909/667700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (1191/12500 : ℝ)) (hi := (3241/20000 : ℝ)) (c := (3337466051981117613/3338500000000000000 : ℝ)) (alpha := (1190453130909/667700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3337466051981117613/3338500000000000000 : ℝ)*(X 0 1+X 2 1)+(1190453130909/667700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (1191/12500 : ℝ)) (hi := (3241/20000 : ℝ)) (c := (3337466051981117613/3338500000000000000 : ℝ)) (alpha := (1190453130909/667700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3337466051981117613/3338500000000000000 : ℝ)*(X 0 2+X 1 2)+(1190453130909/667700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (1191/12500 : ℝ)) (hi := (3241/20000 : ℝ)) (c := (3337466051981117613/3338500000000000000 : ℝ)) (alpha := (1190453130909/667700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056977241/5000000000 : ℝ)*X 0 0+(677381057/1250000000 : ℝ)*X 0 1+(1048231029/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675668261/5000000000 : ℝ)*X 1 0+(-2204693229/10000000000 : ℝ)*X 1 1+(327572203/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351336467/10000000000 : ℝ)*X 2 0+(2620577851/5000000000 : ℝ)*X 2 1+(-2204692703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348149029/10000000000 : ℝ)*X 0 0+(834222301/2000000000 : ℝ)*X 0 1+(1133116723/2500000000 : ℝ)*X 0 2+(4348149029/10000000000 : ℝ)*X 1 0+(834222301/2000000000 : ℝ)*X 1 1+(1133116723/2500000000 : ℝ)*X 1 2+(4348149029/10000000000 : ℝ)*X 2 0+(834222301/2000000000 : ℝ)*X 2 1+(1133116723/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2113968569/10000000000 : ℝ)*X 0 0+(2620899561/5000000000 : ℝ)*X 0 1+(2709200441/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652965119/5000000000 : ℝ)*X 1 0+(-1013723761/5000000000 : ℝ)*X 1 1+(338650069/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305930333/10000000000 : ℝ)*X 2 0+(1083680203/2000000000 : ℝ)*X 2 1+(-506861879/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348177169/10000000000 : ℝ)*X 0 0+(2265579739/5000000000 : ℝ)*X 0 1+(4172425533/10000000000 : ℝ)*X 0 2+(4348177169/10000000000 : ℝ)*X 1 0+(2265579739/5000000000 : ℝ)*X 1 1+(4172425533/10000000000 : ℝ)*X 1 2+(4348177169/10000000000 : ℝ)*X 2 0+(2265579739/5000000000 : ℝ)*X 2 1+(4172425533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (590698785781588913388917163/83462500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (889387341/100000000000000 : ℝ)*(base19) + (495791253/100000000000000 : ℝ)*(base23) + (213884123/100000000000000 : ℝ)*(lower2) + (9065067/25000000000000 : ℝ)*(upper5) + (2097197140750039/50000000000000 : ℝ)*(major0) + (2097197140750039/50000000000000 : ℝ)*(major1) + (2097197140750039/50000000000000 : ℝ)*(major2) + (562137553102271/10000000000000 : ℝ)*(sp0) + (5621401787351301/100000000000000 : ℝ)*(sp1) + (175669053359963/3125000000000 : ℝ)*(sp2) + (691841966907943/25000000000000 : ℝ)*(sp3) + (34672287359/100000000000000 : ℝ)*(sp4) + (7526571427/100000000000000 : ℝ)*(sp5) + (205122889/2000000000000 : ℝ)*(sp7) + (138368906188811/5000000000000 : ℝ)*(f.failure) + (5621410203310069/100000000000000 : ℝ)*(f.sum) + (103381654329693/33385000000000000000000000000 : ℝ)*base66 + (1118865825796558093/166925000000000000000000000000000 : ℝ)*base68 + (2077826505178758093/166925000000000000000000000000000 : ℝ)*base70 + (2483138453777458093/166925000000000000000000000000000 : ℝ)*base72 + (84775097622157/33385000000000000000000000000 : ℝ)*base73 + (2087180893374658093/166925000000000000000000000000000 : ℝ)*base76 + (1895201616011158093/166925000000000000000000000000000 : ℝ)*base78 + (3102995512984008093/166925000000000000000000000000000 : ℝ)*base80 + (35744307113777/8346250000000000000000000000 : ℝ)*base82 + (8512393/500000000000000000000 : ℝ)*base90 + (8512393/500000000000000000000 : ℝ)*base92 + (8512393/500000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11712289260024052058919/3338500000000000000000000000 : ℝ) := by norm_num
    linear_combination (614513/400000000000 : ℝ)*(base19) + (209312851/50000000000000 : ℝ)*(base23) + (16121729/12500000000000 : ℝ)*(upper3) + (57512919/100000000000000 : ℝ)*(lower4) + (296633/12500000000000 : ℝ)*(upper5) + (13203181653429/312500000000 : ℝ)*(major0) + (13203181653429/312500000000 : ℝ)*(major1) + (13203181653429/312500000000 : ℝ)*(major2) + (1893384907/50000000000000 : ℝ)*(sp1) + (5119781333/50000000000000 : ℝ)*(sp2) + (2831226505227873/50000000000000 : ℝ)*(sp4) + (5662449070057683/100000000000000 : ℝ)*(sp5) + (5662442352267379/100000000000000 : ℝ)*(sp6) + (1393791565398587/50000000000000 : ℝ)*(sp7) + (1393791565398587/50000000000000 : ℝ)*(f.failure) + (2831226505227873/50000000000000 : ℝ)*(f.sum) + (1726521940073/333850000000000000000000000 : ℝ)*base66 + (2350866632523727/1043281250000000000000000000000 : ℝ)*base67 + (13696817547606829/2086562500000000000000000000000 : ℝ)*base69 + (3698471880774699/521640625000000000000000000000 : ℝ)*base72 + (207998525117/52164062500000000000000000 : ℝ)*base74 + (22143227574881921/2086562500000000000000000000000 : ℝ)*base76 + (36101116630734467/4173125000000000000000000000000 : ℝ)*base78 + (6838846667104283/4173125000000000000000000000000 : ℝ)*base79 + (1496459312511/1669250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2445081/5000000000000000000000 : ℝ)*base90 + (2445081/5000000000000000000000 : ℝ)*base92 + (2445081/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1249_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3241/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1191/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10929/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1249_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1249_s4_0 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-423241263/2000000000 : ℝ)*x 0 + (5397210307/10000000000 : ℝ)*x 1 + (1315379311/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423241263/2000000000 : ℝ)^4221 ≤ (12868681301103/100000000000000 : ℝ)^3197 := by
    have hnat : (423241263 : ℕ)^4221*100000000000000^3197 ≤ 12868681301103^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423241263 2000000000 12868681301103 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397210307/10000000000 : ℝ)^4221 ≤ (44297896653219/100000000000000 : ℝ)^3197 := by
    have hnat : (5397210307 : ℕ)^4221*100000000000000^3197 ≤ 44297896653219^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397210307 10000000000 44297896653219 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315379311/2500000000 : ℝ)^4221 ≤ (21416711015187/50000000000000 : ℝ)^3197 := by
    have hnat : (1315379311 : ℕ)^4221*50000000000000^3197 ≤ 21416711015187^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315379311 2500000000 21416711015187 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423241263/2000000000 : ℝ), (5397210307/10000000000 : ℝ), (1315379311/2500000000 : ℝ)] ![(12868681301103/100000000000000 : ℝ), (44297896653219/100000000000000 : ℝ), (21416711015187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423241263/2000000000 : ℝ)|^4221 ≤ (12868681301103/100000000000000 : ℝ)^3197
        have hw : |(-423241263/2000000000 : ℝ)|=(423241263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397210307/10000000000 : ℝ)|^4221 ≤ (44297896653219/100000000000000 : ℝ)^3197
        have hw : |(5397210307/10000000000 : ℝ)|=(5397210307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315379311/2500000000 : ℝ)|^4221 ≤ (21416711015187/50000000000000 : ℝ)^3197
        have hw : |(1315379311/2500000000 : ℝ)|=(1315379311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s4_1 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534582697/1000000000 : ℝ)*x 0 + (-1092547989/5000000000 : ℝ)*x 1 + (5261517241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534582697/1000000000 : ℝ)^4221 ≤ (43741935199663/100000000000000 : ℝ)^3197 := by
    have hnat : (534582697 : ℕ)^4221*100000000000000^3197 ≤ 43741935199663^3197*1000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534582697 1000000000 43741935199663 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092547989/5000000000 : ℝ)^4221 ≤ (6712321393623/50000000000000 : ℝ)^3197 := by
    have hnat : (1092547989 : ℕ)^4221*50000000000000^3197 ≤ 6712321393623^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092547989 5000000000 6712321393623 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261517241/10000000000 : ℝ)^4221 ≤ (2677088874883/6250000000000 : ℝ)^3197 := by
    have hnat : (5261517241 : ℕ)^4221*6250000000000^3197 ≤ 2677088874883^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261517241 10000000000 2677088874883 6250000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534582697/1000000000 : ℝ), (-1092547989/5000000000 : ℝ), (5261517241/10000000000 : ℝ)] ![(43741935199663/100000000000000 : ℝ), (6712321393623/50000000000000 : ℝ), (2677088874883/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534582697/1000000000 : ℝ)|^4221 ≤ (43741935199663/100000000000000 : ℝ)^3197
        have hw : |(534582697/1000000000 : ℝ)|=(534582697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1092547989/5000000000 : ℝ)|^4221 ≤ (6712321393623/50000000000000 : ℝ)^3197
        have hw : |(-1092547989/5000000000 : ℝ)|=(1092547989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261517241/10000000000 : ℝ)|^4221 ≤ (2677088874883/6250000000000 : ℝ)^3197
        have hw : |(5261517241/10000000000 : ℝ)|=(5261517241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s4_2 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106916539/200000000 : ℝ)*x 0 + (5261517263/10000000000 : ℝ)*x 1 + (-273136997/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106916539/200000000 : ℝ)^4221 ≤ (21870967491799/50000000000000 : ℝ)^3197 := by
    have hnat : (106916539 : ℕ)^4221*50000000000000^3197 ≤ 21870967491799^3197*200000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106916539 200000000 21870967491799 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261517263/10000000000 : ℝ)^4221 ≤ (21416711117297/50000000000000 : ℝ)^3197 := by
    have hnat : (5261517263 : ℕ)^4221*50000000000000^3197 ≤ 21416711117297^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261517263 10000000000 21416711117297 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273136997/1250000000 : ℝ)^4221 ≤ (13424642771023/100000000000000 : ℝ)^3197 := by
    have hnat : (273136997 : ℕ)^4221*100000000000000^3197 ≤ 13424642771023^3197*1250000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273136997 1250000000 13424642771023 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106916539/200000000 : ℝ), (5261517263/10000000000 : ℝ), (-273136997/1250000000 : ℝ)] ![(21870967491799/50000000000000 : ℝ), (21416711117297/50000000000000 : ℝ), (13424642771023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106916539/200000000 : ℝ)|^4221 ≤ (21870967491799/50000000000000 : ℝ)^3197
        have hw : |(106916539/200000000 : ℝ)|=(106916539/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261517263/10000000000 : ℝ)|^4221 ≤ (21416711117297/50000000000000 : ℝ)^3197
        have hw : |(5261517263/10000000000 : ℝ)|=(5261517263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273136997/1250000000 : ℝ)|^4221 ≤ (13424642771023/100000000000000 : ℝ)^3197
        have hw : |(-273136997/1250000000 : ℝ)|=(273136997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s4_3 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (271843641/625000000 : ℝ)*x 0 + (4213799699/10000000000 : ℝ)*x 1 + (448943471/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271843641/625000000 : ℝ)^4221 ≤ (52053645317/156250000000 : ℝ)^3197 := by
    have hnat : (271843641 : ℕ)^4221*156250000000^3197 ≤ 52053645317^3197*625000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271843641 625000000 52053645317 156250000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4213799699/10000000000 : ℝ)^4221 ≤ (1597448378007/5000000000000 : ℝ)^3197 := by
    have hnat : (4213799699 : ℕ)^4221*5000000000000^3197 ≤ 1597448378007^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213799699 10000000000 1597448378007 5000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448943471/1000000000 : ℝ)^4221 ≤ (6947339885397/20000000000000 : ℝ)^3197 := by
    have hnat : (448943471 : ℕ)^4221*20000000000000^3197 ≤ 6947339885397^3197*1000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448943471 1000000000 6947339885397 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271843641/625000000 : ℝ), (4213799699/10000000000 : ℝ), (448943471/1000000000 : ℝ)] ![(52053645317/156250000000 : ℝ), (1597448378007/5000000000000 : ℝ), (6947339885397/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271843641/625000000 : ℝ)|^4221 ≤ (52053645317/156250000000 : ℝ)^3197
        have hw : |(271843641/625000000 : ℝ)|=(271843641/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4213799699/10000000000 : ℝ)|^4221 ≤ (1597448378007/5000000000000 : ℝ)^3197
        have hw : |(4213799699/10000000000 : ℝ)|=(4213799699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448943471/1000000000 : ℝ)|^4221 ≤ (6947339885397/20000000000000 : ℝ)^3197
        have hw : |(448943471/1000000000 : ℝ)|=(448943471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s4_4 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1058106383/5000000000 : ℝ)*x 0 + (5261892383/10000000000 : ℝ)*x 1 + (5396833427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058106383/5000000000 : ℝ)^4221 ≤ (3217183273673/25000000000000 : ℝ)^3197 := by
    have hnat : (1058106383 : ℕ)^4221*25000000000000^3197 ≤ 3217183273673^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058106383 5000000000 3217183273673 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261892383/10000000000 : ℝ)^4221 ≤ (2141872711333/5000000000000 : ℝ)^3197 := by
    have hnat : (5261892383 : ℕ)^4221*5000000000000^3197 ≤ 2141872711333^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261892383 10000000000 2141872711333 5000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396833427/10000000000 : ℝ)^4221 ≤ (22146906331399/50000000000000 : ℝ)^3197 := by
    have hnat : (5396833427 : ℕ)^4221*50000000000000^3197 ≤ 22146906331399^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396833427 10000000000 22146906331399 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1058106383/5000000000 : ℝ), (5261892383/10000000000 : ℝ), (5396833427/10000000000 : ℝ)] ![(3217183273673/25000000000000 : ℝ), (2141872711333/5000000000000 : ℝ), (22146906331399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1058106383/5000000000 : ℝ)|^4221 ≤ (3217183273673/25000000000000 : ℝ)^3197
        have hw : |(-1058106383/5000000000 : ℝ)|=(1058106383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261892383/10000000000 : ℝ)|^4221 ≤ (2141872711333/5000000000000 : ℝ)^3197
        have hw : |(5261892383/10000000000 : ℝ)|=(5261892383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396833427/10000000000 : ℝ)|^4221 ≤ (22146906331399/50000000000000 : ℝ)^3197
        have hw : |(5396833427/10000000000 : ℝ)|=(5396833427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s4_5 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311189819/10000000000 : ℝ)*x 0 + (-2049779859/10000000000 : ℝ)*x 1 + (5396833337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311189819/10000000000 : ℝ)^4221 ≤ (43368129063299/100000000000000 : ℝ)^3197 := by
    have hnat : (5311189819 : ℕ)^4221*100000000000000^3197 ≤ 43368129063299^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311189819 10000000000 43368129063299 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2049779859/10000000000 : ℝ)^4221 ≤ (9870447383/80000000000 : ℝ)^3197 := by
    have hnat : (2049779859 : ℕ)^4221*80000000000^3197 ≤ 9870447383^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049779859 10000000000 9870447383 80000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396833337/10000000000 : ℝ)^4221 ≤ (44293811687541/100000000000000 : ℝ)^3197 := by
    have hnat : (5396833337 : ℕ)^4221*100000000000000^3197 ≤ 44293811687541^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396833337 10000000000 44293811687541 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311189819/10000000000 : ℝ), (-2049779859/10000000000 : ℝ), (5396833337/10000000000 : ℝ)] ![(43368129063299/100000000000000 : ℝ), (9870447383/80000000000 : ℝ), (44293811687541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311189819/10000000000 : ℝ)|^4221 ≤ (43368129063299/100000000000000 : ℝ)^3197
        have hw : |(5311189819/10000000000 : ℝ)|=(5311189819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2049779859/10000000000 : ℝ)|^4221 ≤ (9870447383/80000000000 : ℝ)^3197
        have hw : |(-2049779859/10000000000 : ℝ)|=(2049779859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396833337/10000000000 : ℝ)|^4221 ≤ (44293811687541/100000000000000 : ℝ)^3197
        have hw : |(5396833337/10000000000 : ℝ)|=(5396833337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s4_6 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062237849/2000000000 : ℝ)*x 0 + (2698417037/5000000000 : ℝ)*x 1 + (-1024889817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062237849/2000000000 : ℝ)^4221 ≤ (5421015359389/12500000000000 : ℝ)^3197 := by
    have hnat : (1062237849 : ℕ)^4221*12500000000000^3197 ≤ 5421015359389^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062237849 2000000000 5421015359389 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698417037/5000000000 : ℝ)^4221 ≤ (5536727459227/12500000000000 : ℝ)^3197 := by
    have hnat : (2698417037 : ℕ)^4221*12500000000000^3197 ≤ 5536727459227^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698417037 5000000000 5536727459227 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024889817/5000000000 : ℝ)^4221 ≤ (12338057440637/100000000000000 : ℝ)^3197 := by
    have hnat : (1024889817 : ℕ)^4221*100000000000000^3197 ≤ 12338057440637^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024889817 5000000000 12338057440637 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062237849/2000000000 : ℝ), (2698417037/5000000000 : ℝ), (-1024889817/5000000000 : ℝ)] ![(5421015359389/12500000000000 : ℝ), (5536727459227/12500000000000 : ℝ), (12338057440637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062237849/2000000000 : ℝ)|^4221 ≤ (5421015359389/12500000000000 : ℝ)^3197
        have hw : |(1062237849/2000000000 : ℝ)|=(1062237849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698417037/5000000000 : ℝ)|^4221 ≤ (5536727459227/12500000000000 : ℝ)^3197
        have hw : |(2698417037/5000000000 : ℝ)|=(2698417037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1024889817/5000000000 : ℝ)|^4221 ≤ (12338057440637/100000000000000 : ℝ)^3197
        have hw : |(-1024889817/5000000000 : ℝ)|=(1024889817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s4_7 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2174755421/5000000000 : ℝ)*x 0 + (897734597/2000000000 : ℝ)*x 1 + (4214564283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174755421/5000000000 : ℝ)^4221 ≤ (4164307535083/12500000000000 : ℝ)^3197 := by
    have hnat : (2174755421 : ℕ)^4221*12500000000000^3197 ≤ 4164307535083^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174755421 5000000000 4164307535083 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897734597/2000000000 : ℝ)^4221 ≤ (4341114757239/12500000000000 : ℝ)^3197 := by
    have hnat : (897734597 : ℕ)^4221*12500000000000^3197 ≤ 4341114757239^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897734597 2000000000 4341114757239 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4214564283/10000000000 : ℝ)^4221 ≤ (1278264865947/4000000000000 : ℝ)^3197 := by
    have hnat : (4214564283 : ℕ)^4221*4000000000000^3197 ≤ 1278264865947^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214564283 10000000000 1278264865947 4000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174755421/5000000000 : ℝ), (897734597/2000000000 : ℝ), (4214564283/10000000000 : ℝ)] ![(4164307535083/12500000000000 : ℝ), (4341114757239/12500000000000 : ℝ), (1278264865947/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174755421/5000000000 : ℝ)|^4221 ≤ (4164307535083/12500000000000 : ℝ)^3197
        have hw : |(2174755421/5000000000 : ℝ)|=(2174755421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897734597/2000000000 : ℝ)|^4221 ≤ (4341114757239/12500000000000 : ℝ)^3197
        have hw : |(897734597/2000000000 : ℝ)|=(897734597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4214564283/10000000000 : ℝ)|^4221 ≤ (1278264865947/4000000000000 : ℝ)^3197
        have hw : |(4214564283/10000000000 : ℝ)|=(4214564283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1249_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10929/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11363/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7347/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10929/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7347/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10929/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7347/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10929/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7347/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10929/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7347/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10929/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7347/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10929/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10929/100000 : ℝ) ^ (8441/2048 : ℝ) ≤ (2725024227444893/25000000000000000000 : ℝ) := by
    have hpowers : (10929/100000 : ℝ)^8441 ≤ (2725024227444893/25000000000000000000 : ℝ)^2048 := by
      have hnat : (10929 : ℕ)^8441*25000000000000000000^2048 ≤ 2725024227444893^2048*100000^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10929 100000 2725024227444893 25000000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10929/100000 : ℝ)) (X := (2725024227444893/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7347/50000 : ℝ) ^ (8441/2048 : ℝ) ≤ (7384640052526721/20000000000000000000 : ℝ) := by
    have hpowers : (7347/50000 : ℝ)^8441 ≤ (7384640052526721/20000000000000000000 : ℝ)^2048 := by
      have hnat : (7347 : ℕ)^8441*20000000000000000000^2048 ≤ 7384640052526721^2048*50000^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7347 50000 7384640052526721 20000000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7347/50000 : ℝ)) (X := (7384640052526721/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502725024227444893/12500000000000000000 : ℝ) ≤ (10000528884156091/10000000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (12502725024227444893/12500000000000000000 : ℝ)^2048 ≤ (10000528884156091/10000000000000000 : ℝ)^8441 := by
      have hnat : (12502725024227444893 : ℕ)^2048*10000000000000000^8441 ≤ 10000528884156091^8441*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502725024227444893 12500000000000000000 10000528884156091 10000000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000528884156091/10000000000000000 : ℝ)) (X := (12502725024227444893/12500000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047823297172413177/100000000000000000000 : ℝ) ≤ (2000232020803657/2000000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (100047823297172413177/100000000000000000000 : ℝ)^2048 ≤ (2000232020803657/2000000000000000 : ℝ)^8441 := by
      have hnat : (100047823297172413177 : ℕ)^2048*2000000000000000^8441 ≤ 2000232020803657^8441*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047823297172413177 100000000000000000000 2000232020803657 2000000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000232020803657/2000000000000000 : ℝ)) (X := (100047823297172413177/100000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007384640052526721/10000000000000000000 : ℝ) ≤ (10001791323880479/10000000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (10007384640052526721/10000000000000000000 : ℝ)^2048 ≤ (10001791323880479/10000000000000000 : ℝ)^8441 := by
      have hnat : (10007384640052526721 : ℕ)^2048*10000000000000000^8441 ≤ 10001791323880479^8441*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007384640052526721 10000000000000000000 10001791323880479 10000000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001791323880479/10000000000000000 : ℝ)) (X := (10007384640052526721/10000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2725024227444893/25000000000000000000 : ℝ) ≤ ((12546064681699948721/12550000000000000000 : ℝ)+2*(315609931097/188250000000000 : ℝ)*(10929/100000 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (12546064681699948721/12550000000000000000 : ℝ)+2*(315609931097/188250000000000 : ℝ)*(10929/100000 : ℝ)=(10000528884156091/10000000000000000 : ℝ) by norm_num, show 1+2*(2725024227444893/25000000000000000000 : ℝ)=(12502725024227444893/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7384640052526721/20000000000000000000 : ℝ)+(2725024227444893/25000000000000000000 : ℝ) ≤ ((12546064681699948721/12550000000000000000 : ℝ)+(315609931097/188250000000000 : ℝ)*((7347/50000 : ℝ)+(10929/100000 : ℝ)))^(8441/2048 : ℝ) := by
    rw [show (12546064681699948721/12550000000000000000 : ℝ)+(315609931097/188250000000000 : ℝ)*((7347/50000 : ℝ)+(10929/100000 : ℝ))=(2000232020803657/2000000000000000 : ℝ) by norm_num, show 1+(7384640052526721/20000000000000000000 : ℝ)+(2725024227444893/25000000000000000000 : ℝ)=(100047823297172413177/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7384640052526721/20000000000000000000 : ℝ) ≤ ((12546064681699948721/12550000000000000000 : ℝ)+2*(315609931097/188250000000000 : ℝ)*(7347/50000 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (12546064681699948721/12550000000000000000 : ℝ)+2*(315609931097/188250000000000 : ℝ)*(7347/50000 : ℝ)=(10001791323880479/10000000000000000 : ℝ) by norm_num, show 1+2*(7384640052526721/20000000000000000000 : ℝ)=(10007384640052526721/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12546064681699948721/12550000000000000000 : ℝ)*(X 1 0+X 2 0)+(315609931097/188250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (10929/100000 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (12546064681699948721/12550000000000000000 : ℝ)) (alpha := (315609931097/188250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12546064681699948721/12550000000000000000 : ℝ)*(X 0 1+X 2 1)+(315609931097/188250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (10929/100000 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (12546064681699948721/12550000000000000000 : ℝ)) (alpha := (315609931097/188250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12546064681699948721/12550000000000000000 : ℝ)*(X 0 2+X 1 2)+(315609931097/188250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (10929/100000 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (12546064681699948721/12550000000000000000 : ℝ)) (alpha := (315609931097/188250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-423241263/2000000000 : ℝ)*X 0 0+(5397210307/10000000000 : ℝ)*X 0 1+(1315379311/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534582697/1000000000 : ℝ)*X 1 0+(-1092547989/5000000000 : ℝ)*X 1 1+(5261517241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106916539/200000000 : ℝ)*X 2 0+(5261517263/10000000000 : ℝ)*X 2 1+(-273136997/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271843641/625000000 : ℝ)*X 0 0+(4213799699/10000000000 : ℝ)*X 0 1+(448943471/1000000000 : ℝ)*X 0 2+(271843641/625000000 : ℝ)*X 1 0+(4213799699/10000000000 : ℝ)*X 1 1+(448943471/1000000000 : ℝ)*X 1 2+(271843641/625000000 : ℝ)*X 2 0+(4213799699/10000000000 : ℝ)*X 2 1+(448943471/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1058106383/5000000000 : ℝ)*X 0 0+(5261892383/10000000000 : ℝ)*X 0 1+(5396833427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311189819/10000000000 : ℝ)*X 1 0+(-2049779859/10000000000 : ℝ)*X 1 1+(5396833337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062237849/2000000000 : ℝ)*X 2 0+(2698417037/5000000000 : ℝ)*X 2 1+(-1024889817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174755421/5000000000 : ℝ)*X 0 0+(897734597/2000000000 : ℝ)*X 0 1+(4214564283/10000000000 : ℝ)*X 0 2+(2174755421/5000000000 : ℝ)*X 1 0+(897734597/2000000000 : ℝ)*X 1 1+(4214564283/10000000000 : ℝ)*X 1 2+(2174755421/5000000000 : ℝ)*X 2 0+(897734597/2000000000 : ℝ)*X 2 1+(4214564283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1346768228895278656621776783/156875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1701577519/100000000000000 : ℝ)*(base19) + (1539156251/100000000000000 : ℝ)*(base23) + (18022069/25000000000000 : ℝ)*(lower2) + (220293389/100000000000000 : ℝ)*(upper3) + (118438973/100000000000000 : ℝ)*(upper5) + (1374711562915741/25000000000000 : ℝ)*(major0) + (1374711562915741/25000000000000 : ℝ)*(major1) + (1374711562915741/25000000000000 : ℝ)*(major2) + (1842404855867267/25000000000000 : ℝ)*(sp0) + (184241521605063/2500000000000 : ℝ)*(sp1) + (7369661026623787/100000000000000 : ℝ)*(sp2) + (1814003301007151/50000000000000 : ℝ)*(sp3) + (43142310971/100000000000000 : ℝ)*(sp4) + (2304936569/10000000000000 : ℝ)*(sp7) + (453503706422499/12500000000000 : ℝ)*(f.failure) + (3684831282890019/50000000000000 : ℝ)*(f.sum) + (9353641682033/9412500000000000000000000000 : ℝ)*base65 + (886377016530301783/941250000000000000000000000000000 : ℝ)*base67 + (5374263946777198217/941250000000000000000000000000000 : ℝ)*base70 + (7521874033061551783/941250000000000000000000000000000 : ℝ)*base71 + (4677637457771/4706250000000000000000000000 : ℝ)*base74 + (17414179655005948217/941250000000000000000000000000000 : ℝ)*base76 + (1041331621000948217/941250000000000000000000000000000 : ℝ)*base78 + (2012124434264698217/941250000000000000000000000000000 : ℝ)*base80 + (6320524813583/9412500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2066863/1250000000000000000000 : ℝ)*base89 + (2066863/1250000000000000000000 : ℝ)*base91 + (2066863/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (392857193017136496340109001/125500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1049482063/100000000000000 : ℝ)*(base19) + (399439853/100000000000000 : ℝ)*(base23) + (1563611/2000000000000 : ℝ)*(upper2) + (416398517/100000000000000 : ℝ)*(upper3) + (38560581/50000000000000 : ℝ)*(upper4) + (20831501/100000000000000 : ℝ)*(upper5) + (1105881120010227/20000000000000 : ℝ)*(major0) + (1105881120010227/20000000000000 : ℝ)*(major1) + (1105881120010227/20000000000000 : ℝ)*(major2) + (22824943137/100000000000000 : ℝ)*(sp2) + (926327374081891/12500000000000 : ℝ)*(sp4) + (1482123588634613/20000000000000 : ℝ)*(sp5) + (3705297884136069/50000000000000 : ℝ)*(sp6) + (912048025775647/25000000000000 : ℝ)*(sp7) + (912048025775647/25000000000000 : ℝ)*(f.failure) + (926327374081891/12500000000000 : ℝ)*(f.sum) + (8664487467053/627500000000000000000000000 : ℝ)*base65 + (146528461373830333/251000000000000000000000000000000 : ℝ)*base68 + (2348389028229830333/251000000000000000000000000000000 : ℝ)*base70 + (2749099552250830333/251000000000000000000000000000000 : ℝ)*base72 + (4759406601371/1255000000000000000000000000 : ℝ)*base73 + (6065355805271169667/251000000000000000000000000000000 : ℝ)*base75 + (8318255606225830333/251000000000000000000000000000000 : ℝ)*base78 + (1406404969657169667/251000000000000000000000000000000 : ℝ)*base79 + (1319715959173/627500000000000000000000000 : ℝ)*base81 + (18357861/2500000000000000000000 : ℝ)*base90 + (18357861/2500000000000000000000 : ℝ)*base92 + (18357861/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1249_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10929/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1249_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1249_s5_0 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116645083/10000000000 : ℝ)*x 0 + (2696120119/5000000000 : ℝ)*x 1 + (105323977/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116645083/10000000000 : ℝ)^4221 ≤ (2574440836661/20000000000000 : ℝ)^3197 := by
    have hnat : (2116645083 : ℕ)^4221*20000000000000^3197 ≤ 2574440836661^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116645083 10000000000 2574440836661 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696120119/5000000000 : ℝ)^4221 ≤ (44244046761719/100000000000000 : ℝ)^3197 := by
    have hnat : (2696120119 : ℕ)^4221*100000000000000^3197 ≤ 44244046761719^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696120119 5000000000 44244046761719 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105323977/200000000 : ℝ)^4221 ≤ (5360468631373/12500000000000 : ℝ)^3197 := by
    have hnat : (105323977 : ℕ)^4221*12500000000000^3197 ≤ 5360468631373^3197*200000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105323977 200000000 5360468631373 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116645083/10000000000 : ℝ), (2696120119/5000000000 : ℝ), (105323977/200000000 : ℝ)] ![(2574440836661/20000000000000 : ℝ), (44244046761719/100000000000000 : ℝ), (5360468631373/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116645083/10000000000 : ℝ)|^4221 ≤ (2574440836661/20000000000000 : ℝ)^3197
        have hw : |(-2116645083/10000000000 : ℝ)|=(2116645083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696120119/5000000000 : ℝ)|^4221 ≤ (44244046761719/100000000000000 : ℝ)^3197
        have hw : |(2696120119/5000000000 : ℝ)|=(2696120119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105323977/200000000 : ℝ)|^4221 ≤ (5360468631373/12500000000000 : ℝ)^3197
        have hw : |(105323977/200000000 : ℝ)|=(105323977/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s5_1 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672284319/5000000000 : ℝ)*x 0 + (-2180565939/10000000000 : ℝ)*x 1 + (5266198857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672284319/5000000000 : ℝ)^4221 ≤ (349826732749/800000000000 : ℝ)^3197 := by
    have hnat : (2672284319 : ℕ)^4221*800000000000^3197 ≤ 349826732749^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672284319 5000000000 349826732749 800000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2180565939/10000000000 : ℝ)^4221 ≤ (6693954631653/50000000000000 : ℝ)^3197 := by
    have hnat : (2180565939 : ℕ)^4221*50000000000000^3197 ≤ 6693954631653^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180565939 10000000000 6693954631653 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266198857/10000000000 : ℝ)^4221 ≤ (10720937281561/25000000000000 : ℝ)^3197 := by
    have hnat : (5266198857 : ℕ)^4221*25000000000000^3197 ≤ 10720937281561^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266198857 10000000000 10720937281561 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672284319/5000000000 : ℝ), (-2180565939/10000000000 : ℝ), (5266198857/10000000000 : ℝ)] ![(349826732749/800000000000 : ℝ), (6693954631653/50000000000000 : ℝ), (10720937281561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672284319/5000000000 : ℝ)|^4221 ≤ (349826732749/800000000000 : ℝ)^3197
        have hw : |(2672284319/5000000000 : ℝ)|=(2672284319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2180565939/10000000000 : ℝ)|^4221 ≤ (6693954631653/50000000000000 : ℝ)^3197
        have hw : |(-2180565939/10000000000 : ℝ)|=(2180565939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266198857/10000000000 : ℝ)|^4221 ≤ (10720937281561/25000000000000 : ℝ)^3197
        have hw : |(5266198857/10000000000 : ℝ)|=(5266198857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s5_2 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672284349/5000000000 : ℝ)*x 0 + (263309943/500000000 : ℝ)*x 1 + (-68142683/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672284349/5000000000 : ℝ)^4221 ≤ (21864171120887/50000000000000 : ℝ)^3197 := by
    have hnat : (2672284349 : ℕ)^4221*50000000000000^3197 ≤ 21864171120887^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672284349 5000000000 21864171120887 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263309943/500000000 : ℝ)^4221 ≤ (21441874579249/50000000000000 : ℝ)^3197 := by
    have hnat : (263309943 : ℕ)^4221*50000000000000^3197 ≤ 21441874579249^3197*500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263309943 500000000 21441874579249 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68142683/312500000 : ℝ)^4221 ≤ (13387908590493/100000000000000 : ℝ)^3197 := by
    have hnat : (68142683 : ℕ)^4221*100000000000000^3197 ≤ 13387908590493^3197*312500000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68142683 312500000 13387908590493 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672284349/5000000000 : ℝ), (263309943/500000000 : ℝ), (-68142683/312500000 : ℝ)] ![(21864171120887/50000000000000 : ℝ), (21441874579249/50000000000000 : ℝ), (13387908590493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672284349/5000000000 : ℝ)|^4221 ≤ (21864171120887/50000000000000 : ℝ)^3197
        have hw : |(2672284349/5000000000 : ℝ)|=(2672284349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263309943/500000000 : ℝ)|^4221 ≤ (21441874579249/50000000000000 : ℝ)^3197
        have hw : |(263309943/500000000 : ℝ)|=(263309943/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68142683/312500000 : ℝ)|^4221 ≤ (13387908590493/100000000000000 : ℝ)^3197
        have hw : |(-68142683/312500000 : ℝ)|=(68142683/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s5_3 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (86995119/200000000 : ℝ)*x 0 + (4223569593/10000000000 : ℝ)*x 1 + (2239799497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86995119/200000000 : ℝ)^4221 ≤ (208230868719/625000000000 : ℝ)^3197 := by
    have hnat : (86995119 : ℕ)^4221*625000000000^3197 ≤ 208230868719^3197*200000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86995119 200000000 208230868719 625000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4223569593/10000000000 : ℝ)^4221 ≤ (32046805354641/100000000000000 : ℝ)^3197 := by
    have hnat : (4223569593 : ℕ)^4221*100000000000000^3197 ≤ 32046805354641^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223569593 10000000000 32046805354641 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239799497/5000000000 : ℝ)^4221 ≤ (17318127816899/50000000000000 : ℝ)^3197 := by
    have hnat : (2239799497 : ℕ)^4221*50000000000000^3197 ≤ 17318127816899^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239799497 5000000000 17318127816899 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86995119/200000000 : ℝ), (4223569593/10000000000 : ℝ), (2239799497/5000000000 : ℝ)] ![(208230868719/625000000000 : ℝ), (32046805354641/100000000000000 : ℝ), (17318127816899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86995119/200000000 : ℝ)|^4221 ≤ (208230868719/625000000000 : ℝ)^3197
        have hw : |(86995119/200000000 : ℝ)|=(86995119/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4223569593/10000000000 : ℝ)|^4221 ≤ (32046805354641/100000000000000 : ℝ)^3197
        have hw : |(4223569593/10000000000 : ℝ)|=(4223569593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2239799497/5000000000 : ℝ)|^4221 ≤ (17318127816899/50000000000000 : ℝ)^3197
        have hw : |(2239799497/5000000000 : ℝ)|=(2239799497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s5_4 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1058325367/5000000000 : ℝ)*x 0 + (2633261123/5000000000 : ℝ)*x 1 + (5391915087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058325367/5000000000 : ℝ)^4221 ≤ (12872249556889/100000000000000 : ℝ)^3197 := by
    have hnat : (1058325367 : ℕ)^4221*100000000000000^3197 ≤ 12872249556889^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058325367 5000000000 12872249556889 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633261123/5000000000 : ℝ)^4221 ≤ (5360903258807/12500000000000 : ℝ)^3197 := by
    have hnat : (2633261123 : ℕ)^4221*12500000000000^3197 ≤ 5360903258807^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633261123 5000000000 5360903258807 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391915087/10000000000 : ℝ)^4221 ≤ (44240524357233/100000000000000 : ℝ)^3197 := by
    have hnat : (5391915087 : ℕ)^4221*100000000000000^3197 ≤ 44240524357233^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391915087 10000000000 44240524357233 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1058325367/5000000000 : ℝ), (2633261123/5000000000 : ℝ), (5391915087/10000000000 : ℝ)] ![(12872249556889/100000000000000 : ℝ), (5360903258807/12500000000000 : ℝ), (44240524357233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1058325367/5000000000 : ℝ)|^4221 ≤ (12872249556889/100000000000000 : ℝ)^3197
        have hw : |(-1058325367/5000000000 : ℝ)|=(1058325367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633261123/5000000000 : ℝ)|^4221 ≤ (5360903258807/12500000000000 : ℝ)^3197
        have hw : |(2633261123/5000000000 : ℝ)|=(2633261123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391915087/10000000000 : ℝ)|^4221 ≤ (44240524357233/100000000000000 : ℝ)^3197
        have hw : |(5391915087/10000000000 : ℝ)|=(5391915087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s5_5 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312395027/10000000000 : ℝ)*x 0 + (-41096969/200000000 : ℝ)*x 1 + (5391914797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312395027/10000000000 : ℝ)^4221 ≤ (21690561329761/50000000000000 : ℝ)^3197 := by
    have hnat : (5312395027 : ℕ)^4221*50000000000000^3197 ≤ 21690561329761^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312395027 10000000000 21690561329761 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41096969/200000000 : ℝ)^4221 ≤ (6189178055599/50000000000000 : ℝ)^3197 := by
    have hnat : (41096969 : ℕ)^4221*50000000000000^3197 ≤ 6189178055599^3197*200000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41096969 200000000 6189178055599 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391914797/10000000000 : ℝ)^4221 ≤ (22120260607827/50000000000000 : ℝ)^3197 := by
    have hnat : (5391914797 : ℕ)^4221*50000000000000^3197 ≤ 22120260607827^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391914797 10000000000 22120260607827 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312395027/10000000000 : ℝ), (-41096969/200000000 : ℝ), (5391914797/10000000000 : ℝ)] ![(21690561329761/50000000000000 : ℝ), (6189178055599/50000000000000 : ℝ), (22120260607827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312395027/10000000000 : ℝ)|^4221 ≤ (21690561329761/50000000000000 : ℝ)^3197
        have hw : |(5312395027/10000000000 : ℝ)|=(5312395027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41096969/200000000 : ℝ)|^4221 ≤ (6189178055599/50000000000000 : ℝ)^3197
        have hw : |(-41096969/200000000 : ℝ)|=(41096969/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391914797/10000000000 : ℝ)|^4221 ≤ (22120260607827/50000000000000 : ℝ)^3197
        have hw : |(5391914797/10000000000 : ℝ)|=(5391914797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s5_6 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062478959/2000000000 : ℝ)*x 0 + (215676579/400000000 : ℝ)*x 1 + (-513712301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062478959/2000000000 : ℝ)^4221 ≤ (43381120158191/100000000000000 : ℝ)^3197 := by
    have hnat : (1062478959 : ℕ)^4221*100000000000000^3197 ≤ 43381120158191^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062478959 2000000000 43381120158191 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215676579/400000000 : ℝ)^4221 ≤ (44240517727419/100000000000000 : ℝ)^3197 := by
    have hnat : (215676579 : ℕ)^4221*100000000000000^3197 ≤ 44240517727419^3197*400000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215676579 400000000 44240517727419 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513712301/2500000000 : ℝ)^4221 ≤ (1547295263513/12500000000000 : ℝ)^3197 := by
    have hnat : (513712301 : ℕ)^4221*12500000000000^3197 ≤ 1547295263513^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513712301 2500000000 1547295263513 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062478959/2000000000 : ℝ), (215676579/400000000 : ℝ), (-513712301/2500000000 : ℝ)] ![(43381120158191/100000000000000 : ℝ), (44240517727419/100000000000000 : ℝ), (1547295263513/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062478959/2000000000 : ℝ)|^4221 ≤ (43381120158191/100000000000000 : ℝ)^3197
        have hw : |(1062478959/2000000000 : ℝ)|=(1062478959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215676579/400000000 : ℝ)|^4221 ≤ (44240517727419/100000000000000 : ℝ)^3197
        have hw : |(215676579/400000000 : ℝ)|=(215676579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-513712301/2500000000 : ℝ)|^4221 ≤ (1547295263513/12500000000000 : ℝ)^3197
        have hw : |(-513712301/2500000000 : ℝ)|=(513712301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s5_7 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4349765561/10000000000 : ℝ)*x 0 + (4478941203/10000000000 : ℝ)*x 1 + (4224230167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349765561/10000000000 : ℝ)^4221 ≤ (33317036189531/100000000000000 : ℝ)^3197 := by
    have hnat : (4349765561 : ℕ)^4221*100000000000000^3197 ≤ 33317036189531^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349765561 10000000000 33317036189531 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478941203/10000000000 : ℝ)^4221 ≤ (6925908138479/20000000000000 : ℝ)^3197 := by
    have hnat : (4478941203 : ℕ)^4221*20000000000000^3197 ≤ 6925908138479^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478941203 10000000000 6925908138479 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224230167/10000000000 : ℝ)^4221 ≤ (6410684620321/20000000000000 : ℝ)^3197 := by
    have hnat : (4224230167 : ℕ)^4221*20000000000000^3197 ≤ 6410684620321^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224230167 10000000000 6410684620321 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349765561/10000000000 : ℝ), (4478941203/10000000000 : ℝ), (4224230167/10000000000 : ℝ)] ![(33317036189531/100000000000000 : ℝ), (6925908138479/20000000000000 : ℝ), (6410684620321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349765561/10000000000 : ℝ)|^4221 ≤ (33317036189531/100000000000000 : ℝ)^3197
        have hw : |(4349765561/10000000000 : ℝ)|=(4349765561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478941203/10000000000 : ℝ)|^4221 ≤ (6925908138479/20000000000000 : ℝ)^3197
        have hw : |(4478941203/10000000000 : ℝ)|=(4478941203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224230167/10000000000 : ℝ)|^4221 ≤ (6410684620321/20000000000000 : ℝ)^3197
        have hw : |(4224230167/10000000000 : ℝ)|=(4224230167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s5_8 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1464369/400000000 : ℝ)*x 0 + (739104139/1250000000 : ℝ)*x 1 + (5912928007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1464369/400000000 : ℝ)^4221 ≤ (60702684511/100000000000000 : ℝ)^3197 := by
    have hnat : (1464369 : ℕ)^4221*100000000000000^3197 ≤ 60702684511^3197*400000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464369 400000000 60702684511 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (739104139/1250000000 : ℝ)^4221 ≤ (4996911924109/10000000000000 : ℝ)^3197 := by
    have hnat : (739104139 : ℕ)^4221*10000000000000^3197 ≤ 4996911924109^3197*1250000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739104139 1250000000 4996911924109 10000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5912928007/10000000000 : ℝ)^4221 ≤ (49970178063771/100000000000000 : ℝ)^3197 := by
    have hnat : (5912928007 : ℕ)^4221*100000000000000^3197 ≤ 49970178063771^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5912928007 10000000000 49970178063771 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1464369/400000000 : ℝ), (739104139/1250000000 : ℝ), (5912928007/10000000000 : ℝ)] ![(60702684511/100000000000000 : ℝ), (4996911924109/10000000000000 : ℝ), (49970178063771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1464369/400000000 : ℝ)|^4221 ≤ (60702684511/100000000000000 : ℝ)^3197
        have hw : |(-1464369/400000000 : ℝ)|=(1464369/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(739104139/1250000000 : ℝ)|^4221 ≤ (4996911924109/10000000000000 : ℝ)^3197
        have hw : |(739104139/1250000000 : ℝ)|=(739104139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5912928007/10000000000 : ℝ)|^4221 ≤ (49970178063771/100000000000000 : ℝ)^3197
        have hw : |(5912928007/10000000000 : ℝ)|=(5912928007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1249_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11463/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14133/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11363/100000 : ℝ) ^ (8441/2048 : ℝ) ≤ (12797848005419831/100000000000000000000 : ℝ) := by
    have hpowers : (11363/100000 : ℝ)^8441 ≤ (12797848005419831/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11363 : ℕ)^8441*100000000000000000000^2048 ≤ 12797848005419831^2048*100000^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11363 100000 12797848005419831 100000000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11363/100000 : ℝ)) (X := (12797848005419831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (8441/2048 : ℝ) ≤ (32414911479408339/100000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^8441 ≤ (32414911479408339/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14237 : ℕ)^8441*100000000000000000000^2048 ≤ 32414911479408339^2048*100000^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 32414911479408339 100000000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (32414911479408339/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012797848005419831/50000000000000000000 : ℝ) ≤ (1000062095611/1000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (50012797848005419831/50000000000000000000 : ℝ)^2048 ≤ (1000062095611/1000000000000 : ℝ)^8441 := by
      have hnat : (50012797848005419831 : ℕ)^2048*1000000000000^8441 ≤ 1000062095611^8441*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012797848005419831 50000000000000000000 1000062095611 1000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000062095611/1000000000000 : ℝ)) (X := (50012797848005419831/50000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004521275948482817/10000000000000000000 : ℝ) ≤ (2500274197020033/2500000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (10004521275948482817/10000000000000000000 : ℝ)^2048 ≤ (2500274197020033/2500000000000000 : ℝ)^8441 := by
      have hnat : (10004521275948482817 : ℕ)^2048*2500000000000000^8441 ≤ 2500274197020033^8441*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004521275948482817 10000000000000000000 2500274197020033 2500000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500274197020033/2500000000000000 : ℝ)) (X := (10004521275948482817/10000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032414911479408339/50000000000000000000 : ℝ) ≤ (1250196577506283/1250000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (50032414911479408339/50000000000000000000 : ℝ)^2048 ≤ (1250196577506283/1250000000000000 : ℝ)^8441 := by
      have hnat : (50032414911479408339 : ℕ)^2048*1250000000000000^8441 ≤ 1250196577506283^8441*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032414911479408339 50000000000000000000 1250196577506283 1250000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250196577506283/1250000000000000 : ℝ)) (X := (50032414911479408339/50000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12797848005419831/100000000000000000000 : ℝ) ≤ ((3591371358813365021/3592500000000000000 : ℝ)+2*(118957992533/71850000000000 : ℝ)*(11363/100000 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (3591371358813365021/3592500000000000000 : ℝ)+2*(118957992533/71850000000000 : ℝ)*(11363/100000 : ℝ)=(1000062095611/1000000000000 : ℝ) by norm_num, show 1+2*(12797848005419831/100000000000000000000 : ℝ)=(50012797848005419831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32414911479408339/100000000000000000000 : ℝ)+(12797848005419831/100000000000000000000 : ℝ) ≤ ((3591371358813365021/3592500000000000000 : ℝ)+(118957992533/71850000000000 : ℝ)*((14237/100000 : ℝ)+(11363/100000 : ℝ)))^(8441/2048 : ℝ) := by
    rw [show (3591371358813365021/3592500000000000000 : ℝ)+(118957992533/71850000000000 : ℝ)*((14237/100000 : ℝ)+(11363/100000 : ℝ))=(2500274197020033/2500000000000000 : ℝ) by norm_num, show 1+(32414911479408339/100000000000000000000 : ℝ)+(12797848005419831/100000000000000000000 : ℝ)=(10004521275948482817/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32414911479408339/100000000000000000000 : ℝ) ≤ ((3591371358813365021/3592500000000000000 : ℝ)+2*(118957992533/71850000000000 : ℝ)*(14237/100000 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (3591371358813365021/3592500000000000000 : ℝ)+2*(118957992533/71850000000000 : ℝ)*(14237/100000 : ℝ)=(1250196577506283/1250000000000000 : ℝ) by norm_num, show 1+2*(32414911479408339/100000000000000000000 : ℝ)=(50032414911479408339/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3591371358813365021/3592500000000000000 : ℝ)*(X 1 0+X 2 0)+(118957992533/71850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (3591371358813365021/3592500000000000000 : ℝ)) (alpha := (118957992533/71850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3591371358813365021/3592500000000000000 : ℝ)*(X 0 1+X 2 1)+(118957992533/71850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (3591371358813365021/3592500000000000000 : ℝ)) (alpha := (118957992533/71850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3591371358813365021/3592500000000000000 : ℝ)*(X 0 2+X 1 2)+(118957992533/71850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (3591371358813365021/3592500000000000000 : ℝ)) (alpha := (118957992533/71850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2116645083/10000000000 : ℝ)*X 0 0+(2696120119/5000000000 : ℝ)*X 0 1+(105323977/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672284319/5000000000 : ℝ)*X 1 0+(-2180565939/10000000000 : ℝ)*X 1 1+(5266198857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672284349/5000000000 : ℝ)*X 2 0+(263309943/500000000 : ℝ)*X 2 1+(-68142683/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((86995119/200000000 : ℝ)*X 0 0+(4223569593/10000000000 : ℝ)*X 0 1+(2239799497/5000000000 : ℝ)*X 0 2+(86995119/200000000 : ℝ)*X 1 0+(4223569593/10000000000 : ℝ)*X 1 1+(2239799497/5000000000 : ℝ)*X 1 2+(86995119/200000000 : ℝ)*X 2 0+(4223569593/10000000000 : ℝ)*X 2 1+(2239799497/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1058325367/5000000000 : ℝ)*X 0 0+(2633261123/5000000000 : ℝ)*X 0 1+(5391915087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312395027/10000000000 : ℝ)*X 1 0+(-41096969/200000000 : ℝ)*X 1 1+(5391914797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062478959/2000000000 : ℝ)*X 2 0+(215676579/400000000 : ℝ)*X 2 1+(-513712301/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349765561/10000000000 : ℝ)*X 0 0+(4478941203/10000000000 : ℝ)*X 0 1+(4224230167/10000000000 : ℝ)*X 0 2+(4349765561/10000000000 : ℝ)*X 1 0+(4478941203/10000000000 : ℝ)*X 1 1+(4224230167/10000000000 : ℝ)*X 1 2+(4349765561/10000000000 : ℝ)*X 2 0+(4478941203/10000000000 : ℝ)*X 2 1+(4224230167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1464369/400000000 : ℝ)*X 0 0+(739104139/1250000000 : ℝ)*X 0 1+(5912928007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s5_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (275381851210051767390642941/29937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (551963291/100000000000000 : ℝ)*(lower2) + (21917053/12500000000000 : ℝ)*(lower3) + (6217833/1250000000000 : ℝ)*(lower4) + (15249759/10000000000000 : ℝ)*(lower5) + (5919851871665021/100000000000000 : ℝ)*(major0) + (5919851871665021/100000000000000 : ℝ)*(major1) + (5919851871665021/100000000000000 : ℝ)*(major2) + (396694903472943/5000000000000 : ℝ)*(sp0) + (7933893555019867/100000000000000 : ℝ)*(sp1) + (7933895710027723/100000000000000 : ℝ)*(sp2) + (3905800806065969/100000000000000 : ℝ)*(sp3) + (4537812787/50000000000000 : ℝ)*(sp5) + (6920617719/100000000000000 : ℝ)*(sp6) + (2280593291/50000000000000 : ℝ)*(sp8) + (3905800806065969/100000000000000 : ℝ)*(f.failure) + (7933902630645441/100000000000000 : ℝ)*(f.sum) + (40791527144657/3592500000000000000000000000 : ℝ)*base66 + (84145305907010147/119750000000000000000000000000000 : ℝ)*base67 + (189059023628239853/119750000000000000000000000000000 : ℝ)*base70 + (36170478474739853/119750000000000000000000000000000 : ℝ)*base72 + (1439571380323/3592500000000000000000000000 : ℝ)*base73 + (210038915032489853/119750000000000000000000000000000 : ℝ)*base76 + (2046968843370989853/119750000000000000000000000000000 : ℝ)*base78 + (468053850402739853/119750000000000000000000000000000 : ℝ)*base80 + (10581820738079/1796250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (44492747/10000000000000000000000 : ℝ)*base90 + (44492747/10000000000000000000000 : ℝ)*base92 + (44492747/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8795634362794904952657/2395000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286524667/25000000000000 : ℝ)*(lower2) + (221601967/50000000000000 : ℝ)*(lower3) + (670824493/50000000000000 : ℝ)*(lower4) + (167943231/12500000000000 : ℝ)*(lower5) + (2975256882617003/50000000000000 : ℝ)*(major0) + (2975256882617003/50000000000000 : ℝ)*(major1) + (2975256882617003/50000000000000 : ℝ)*(major2) + (49361177273/100000000000000 : ℝ)*(sp0) + (1636495653/50000000000000 : ℝ)*(sp1) + (996866492932951/12500000000000 : ℝ)*(sp4) + (1594998643999171/20000000000000 : ℝ)*(sp5) + (7974996492987161/100000000000000 : ℝ)*(sp6) + (1963015457532107/50000000000000 : ℝ)*(sp7) + (379708657/2500000000000 : ℝ)*(sp8) + (1963015457532107/50000000000000 : ℝ)*(f.failure) + (7974996492987161/100000000000000 : ℝ)*(f.sum) + (165860029880641/7185000000000000000000000000 : ℝ)*base65 + (20968015018665979/59875000000000000000000000000000 : ℝ)*base68 + (246794379231165979/59875000000000000000000000000000 : ℝ)*base70 + (198267828729209021/59875000000000000000000000000000 : ℝ)*base71 + (11584781901083/3592500000000000000000000000 : ℝ)*base73 + (128882340730209021/59875000000000000000000000000000 : ℝ)*base75 + (2468645663105540979/59875000000000000000000000000000 : ℝ)*base78 + (210514867797959021/59875000000000000000000000000000 : ℝ)*base79 + (15743583713003/3592500000000000000000000000 : ℝ)*base81 + (54592841/5000000000000000000000 : ℝ)*base90 + (54592841/5000000000000000000000 : ℝ)*base92 + (54592841/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1249_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11463/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1249_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1249_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3241/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1191/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11463/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1249_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1249_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1249_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3241/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1191/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11463/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1249_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
