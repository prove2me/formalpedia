-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1128_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:25:55.947629+00:00
-- url     : https://prove2.me/submissions/2e26486c-9aac-4169-b9f2-b7445692019f

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
theorem support_rectangle_w1128_s9_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-67925177/312500000 : ℝ)*x 0 + (1078646177/2000000000 : ℝ)*x 1 + (5265560979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67925177/312500000 : ℝ)^8321 ≤ (3301600293953/25000000000000 : ℝ)^6273 := by
    have hnat : (67925177 : ℕ)^8321*25000000000000^6273 ≤ 3301600293953^6273*312500000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67925177 312500000 3301600293953 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078646177/2000000000 : ℝ)^8321 ≤ (44086281060917/100000000000000 : ℝ)^6273 := by
    have hnat : (1078646177 : ℕ)^8321*100000000000000^6273 ≤ 44086281060917^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078646177 2000000000 44086281060917 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265560979/10000000000 : ℝ)^8321 ≤ (266920735919/625000000000 : ℝ)^6273 := by
    have hnat : (5265560979 : ℕ)^8321*625000000000^6273 ≤ 266920735919^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265560979 10000000000 266920735919 625000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67925177/312500000 : ℝ), (1078646177/2000000000 : ℝ), (5265560979/10000000000 : ℝ)] ![(3301600293953/25000000000000 : ℝ), (44086281060917/100000000000000 : ℝ), (266920735919/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67925177/312500000 : ℝ)|^8321 ≤ (3301600293953/25000000000000 : ℝ)^6273
        have hw : |(-67925177/312500000 : ℝ)|=(67925177/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078646177/2000000000 : ℝ)|^8321 ≤ (44086281060917/100000000000000 : ℝ)^6273
        have hw : |(1078646177/2000000000 : ℝ)|=(1078646177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265560979/10000000000 : ℝ)|^8321 ≤ (266920735919/625000000000 : ℝ)^6273
        have hw : |(5265560979/10000000000 : ℝ)|=(5265560979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s9_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336198353/2500000000 : ℝ)*x 0 + (-2238364823/10000000000 : ℝ)*x 1 + (1316390227/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336198353/2500000000 : ℝ)^8321 ≤ (43561838780707/100000000000000 : ℝ)^6273 := by
    have hnat : (1336198353 : ℕ)^8321*100000000000000^6273 ≤ 43561838780707^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336198353 2500000000 43561838780707 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238364823/10000000000 : ℝ)^8321 ≤ (274616884387/2000000000000 : ℝ)^6273 := by
    have hnat : (2238364823 : ℕ)^8321*2000000000000^6273 ≤ 274616884387^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238364823 10000000000 274616884387 2000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316390227/2500000000 : ℝ)^8321 ≤ (5338414622897/12500000000000 : ℝ)^6273 := by
    have hnat : (1316390227 : ℕ)^8321*12500000000000^6273 ≤ 5338414622897^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316390227 2500000000 5338414622897 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336198353/2500000000 : ℝ), (-2238364823/10000000000 : ℝ), (1316390227/2500000000 : ℝ)] ![(43561838780707/100000000000000 : ℝ), (274616884387/2000000000000 : ℝ), (5338414622897/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336198353/2500000000 : ℝ)|^8321 ≤ (43561838780707/100000000000000 : ℝ)^6273
        have hw : |(1336198353/2500000000 : ℝ)|=(1336198353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2238364823/10000000000 : ℝ)|^8321 ≤ (274616884387/2000000000000 : ℝ)^6273
        have hw : |(-2238364823/10000000000 : ℝ)|=(2238364823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316390227/2500000000 : ℝ)|^8321 ≤ (5338414622897/12500000000000 : ℝ)^6273
        have hw : |(1316390227/2500000000 : ℝ)|=(1316390227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s9_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344793309/10000000000 : ℝ)*x 0 + (2632780481/5000000000 : ℝ)*x 1 + (-279795611/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344793309/10000000000 : ℝ)^8321 ≤ (43561837667149/100000000000000 : ℝ)^6273 := by
    have hnat : (5344793309 : ℕ)^8321*100000000000000^6273 ≤ 43561837667149^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344793309 10000000000 43561837667149 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632780481/5000000000 : ℝ)^8321 ≤ (42707317564143/100000000000000 : ℝ)^6273 := by
    have hnat : (2632780481 : ℕ)^8321*100000000000000^6273 ≤ 42707317564143^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632780481 5000000000 42707317564143 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279795611/1250000000 : ℝ)^8321 ≤ (6865422374129/50000000000000 : ℝ)^6273 := by
    have hnat : (279795611 : ℕ)^8321*50000000000000^6273 ≤ 6865422374129^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279795611 1250000000 6865422374129 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344793309/10000000000 : ℝ), (2632780481/5000000000 : ℝ), (-279795611/1250000000 : ℝ)] ![(43561837667149/100000000000000 : ℝ), (42707317564143/100000000000000 : ℝ), (6865422374129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344793309/10000000000 : ℝ)|^8321 ≤ (43561837667149/100000000000000 : ℝ)^6273
        have hw : |(5344793309/10000000000 : ℝ)|=(5344793309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632780481/5000000000 : ℝ)|^8321 ≤ (42707317564143/100000000000000 : ℝ)^6273
        have hw : |(2632780481/5000000000 : ℝ)|=(2632780481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279795611/1250000000 : ℝ)|^8321 ≤ (6865422374129/50000000000000 : ℝ)^6273
        have hw : |(-279795611/1250000000 : ℝ)|=(279795611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s9_3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (545831479/1250000000 : ℝ)*x 0 + (4241836123/10000000000 : ℝ)*x 1 + (4495134811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545831479/1250000000 : ℝ)^8321 ≤ (6663383106551/20000000000000 : ℝ)^6273 := by
    have hnat : (545831479 : ℕ)^8321*20000000000000^6273 ≤ 6663383106551^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545831479 1250000000 6663383106551 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241836123/10000000000 : ℝ)^8321 ≤ (32059608579081/100000000000000 : ℝ)^6273 := by
    have hnat : (4241836123 : ℕ)^8321*100000000000000^6273 ≤ 32059608579081^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241836123 10000000000 32059608579081 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495134811/10000000000 : ℝ)^8321 ≤ (34623475878903/100000000000000 : ℝ)^6273 := by
    have hnat : (4495134811 : ℕ)^8321*100000000000000^6273 ≤ 34623475878903^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495134811 10000000000 34623475878903 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545831479/1250000000 : ℝ), (4241836123/10000000000 : ℝ), (4495134811/10000000000 : ℝ)] ![(6663383106551/20000000000000 : ℝ), (32059608579081/100000000000000 : ℝ), (34623475878903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545831479/1250000000 : ℝ)|^8321 ≤ (6663383106551/20000000000000 : ℝ)^6273
        have hw : |(545831479/1250000000 : ℝ)|=(545831479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241836123/10000000000 : ℝ)|^8321 ≤ (32059608579081/100000000000000 : ℝ)^6273
        have hw : |(4241836123/10000000000 : ℝ)|=(4241836123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495134811/10000000000 : ℝ)|^8321 ≤ (34623475878903/100000000000000 : ℝ)^6273
        have hw : |(4495134811/10000000000 : ℝ)|=(4495134811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s9_4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086805319/5000000000 : ℝ)*x 0 + (5265881247/10000000000 : ℝ)*x 1 + (5392909409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086805319/5000000000 : ℝ)^8321 ≤ (6603220631699/50000000000000 : ℝ)^6273 := by
    have hnat : (1086805319 : ℕ)^8321*50000000000000^6273 ≤ 6603220631699^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086805319 5000000000 6603220631699 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265881247/10000000000 : ℝ)^8321 ≤ (213553817167/500000000000 : ℝ)^6273 := by
    have hnat : (5265881247 : ℕ)^8321*500000000000^6273 ≤ 213553817167^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265881247 10000000000 213553817167 500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392909409/10000000000 : ℝ)^8321 ≤ (44082795288599/100000000000000 : ℝ)^6273 := by
    have hnat : (5392909409 : ℕ)^8321*100000000000000^6273 ≤ 44082795288599^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392909409 10000000000 44082795288599 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086805319/5000000000 : ℝ), (5265881247/10000000000 : ℝ), (5392909409/10000000000 : ℝ)] ![(6603220631699/50000000000000 : ℝ), (213553817167/500000000000 : ℝ), (44082795288599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086805319/5000000000 : ℝ)|^8321 ≤ (6603220631699/50000000000000 : ℝ)^6273
        have hw : |(-1086805319/5000000000 : ℝ)|=(1086805319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265881247/10000000000 : ℝ)|^8321 ≤ (213553817167/500000000000 : ℝ)^6273
        have hw : |(5265881247/10000000000 : ℝ)|=(5265881247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392909409/10000000000 : ℝ)|^8321 ≤ (44082795288599/100000000000000 : ℝ)^6273
        have hw : |(5392909409/10000000000 : ℝ)|=(5392909409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s9_5 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (34114543/78125000 : ℝ)*x 0 + (898899867/2000000000 : ℝ)*x 1 + (4242473951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34114543/78125000 : ℝ)^8321 ≤ (8329253355383/25000000000000 : ℝ)^6273 := by
    have hnat : (34114543 : ℕ)^8321*25000000000000^6273 ≤ 8329253355383^6273*78125000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34114543 78125000 8329253355383 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898899867/2000000000 : ℝ)^8321 ≤ (34616983298913/100000000000000 : ℝ)^6273 := by
    have hnat : (898899867 : ℕ)^8321*100000000000000^6273 ≤ 34616983298913^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898899867 2000000000 34616983298913 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242473951/10000000000 : ℝ)^8321 ≤ (6413200651779/20000000000000 : ℝ)^6273 := by
    have hnat : (4242473951 : ℕ)^8321*20000000000000^6273 ≤ 6413200651779^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242473951 10000000000 6413200651779 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34114543/78125000 : ℝ), (898899867/2000000000 : ℝ), (4242473951/10000000000 : ℝ)] ![(8329253355383/25000000000000 : ℝ), (34616983298913/100000000000000 : ℝ), (6413200651779/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34114543/78125000 : ℝ)|^8321 ≤ (8329253355383/25000000000000 : ℝ)^6273
        have hw : |(34114543/78125000 : ℝ)|=(34114543/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898899867/2000000000 : ℝ)|^8321 ≤ (34616983298913/100000000000000 : ℝ)^6273
        have hw : |(898899867/2000000000 : ℝ)|=(898899867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242473951/10000000000 : ℝ)|^8321 ≤ (6413200651779/20000000000000 : ℝ)^6273
        have hw : |(4242473951/10000000000 : ℝ)|=(4242473951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1128_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1417/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (351/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (351/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2267/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (351/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2267/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (351/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2267/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (351/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2267/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (351/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2267/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (351/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2267/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2267/20000 : ℝ) ^ (65/16 : ℝ) ≤ (7203730342076231/50000000000000000000 : ℝ) := by
    have hpowers : (2267/20000 : ℝ)^65 ≤ (7203730342076231/50000000000000000000 : ℝ)^16 := by
      have hnat : (2267 : ℕ)^65*50000000000000000000^16 ≤ 7203730342076231^16*20000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2267 20000 7203730342076231 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2267/20000 : ℝ)) (X := (7203730342076231/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hpowhi : (351/2500 : ℝ) ^ (65/16 : ℝ) ≤ (34369948026924089/100000000000000000000 : ℝ) := by
    have hpowers : (351/2500 : ℝ)^65 ≤ (34369948026924089/100000000000000000000 : ℝ)^16 := by
      have hnat : (351 : ℕ)^65*100000000000000000000^16 ≤ 34369948026924089^16*2500^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        351 2500 34369948026924089 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (351/2500 : ℝ)) (X := (34369948026924089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007203730342076231/25000000000000000000 : ℝ) ≤ (2500177303337257/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (25007203730342076231/25000000000000000000 : ℝ)^16 ≤ (2500177303337257/2500000000000000 : ℝ)^65 := by
      have hnat : (25007203730342076231 : ℕ)^16*2500000000000000^65 ≤ 2500177303337257^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007203730342076231 25000000000000000000 2500177303337257 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500177303337257/2500000000000000 : ℝ)) (X := (25007203730342076231/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048777408711076551/100000000000000000000 : ℝ) ≤ (62507502837443/62500000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (100048777408711076551/100000000000000000000 : ℝ)^16 ≤ (62507502837443/62500000000000 : ℝ)^65 := by
      have hnat : (100048777408711076551 : ℕ)^16*62500000000000^65 ≤ 62507502837443^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048777408711076551 100000000000000000000 62507502837443 62500000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62507502837443/62500000000000 : ℝ)) (X := (100048777408711076551/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034369948026924089/50000000000000000000 : ℝ) ≤ (2500422923658183/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50034369948026924089/50000000000000000000 : ℝ)^16 ≤ (2500422923658183/2500000000000000 : ℝ)^65 := by
      have hnat : (50034369948026924089 : ℕ)^16*2500000000000000^65 ≤ 2500422923658183^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034369948026924089 50000000000000000000 2500422923658183 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500422923658183/2500000000000000 : ℝ)) (X := (50034369948026924089/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7203730342076231/50000000000000000000 : ℝ) ≤ ((270407819967583359/270500000000000000 : ℝ)+2*(122810160463/67625000000000 : ℝ)*(2267/20000 : ℝ))^(65/16 : ℝ) := by
    rw [show (270407819967583359/270500000000000000 : ℝ)+2*(122810160463/67625000000000 : ℝ)*(2267/20000 : ℝ)=(2500177303337257/2500000000000000 : ℝ) by norm_num, show 1+2*(7203730342076231/50000000000000000000 : ℝ)=(25007203730342076231/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34369948026924089/100000000000000000000 : ℝ)+(7203730342076231/50000000000000000000 : ℝ) ≤ ((270407819967583359/270500000000000000 : ℝ)+(122810160463/67625000000000 : ℝ)*((351/2500 : ℝ)+(2267/20000 : ℝ)))^(65/16 : ℝ) := by
    rw [show (270407819967583359/270500000000000000 : ℝ)+(122810160463/67625000000000 : ℝ)*((351/2500 : ℝ)+(2267/20000 : ℝ))=(62507502837443/62500000000000 : ℝ) by norm_num, show 1+(34369948026924089/100000000000000000000 : ℝ)+(7203730342076231/50000000000000000000 : ℝ)=(100048777408711076551/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34369948026924089/100000000000000000000 : ℝ) ≤ ((270407819967583359/270500000000000000 : ℝ)+2*(122810160463/67625000000000 : ℝ)*(351/2500 : ℝ))^(65/16 : ℝ) := by
    rw [show (270407819967583359/270500000000000000 : ℝ)+2*(122810160463/67625000000000 : ℝ)*(351/2500 : ℝ)=(2500422923658183/2500000000000000 : ℝ) by norm_num, show 1+2*(34369948026924089/100000000000000000000 : ℝ)=(50034369948026924089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (270407819967583359/270500000000000000 : ℝ)*(X 1 0+X 2 0)+(122810160463/67625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (2267/20000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (270407819967583359/270500000000000000 : ℝ)) (alpha := (122810160463/67625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (270407819967583359/270500000000000000 : ℝ)*(X 0 1+X 2 1)+(122810160463/67625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (2267/20000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (270407819967583359/270500000000000000 : ℝ)) (alpha := (122810160463/67625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (270407819967583359/270500000000000000 : ℝ)*(X 0 2+X 1 2)+(122810160463/67625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (2267/20000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (270407819967583359/270500000000000000 : ℝ)) (alpha := (122810160463/67625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-67925177/312500000 : ℝ)*X 0 0+(1078646177/2000000000 : ℝ)*X 0 1+(5265560979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336198353/2500000000 : ℝ)*X 1 0+(-2238364823/10000000000 : ℝ)*X 1 1+(1316390227/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344793309/10000000000 : ℝ)*X 2 0+(2632780481/5000000000 : ℝ)*X 2 1+(-279795611/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545831479/1250000000 : ℝ)*X 0 0+(4241836123/10000000000 : ℝ)*X 0 1+(4495134811/10000000000 : ℝ)*X 0 2+(545831479/1250000000 : ℝ)*X 1 0+(4241836123/10000000000 : ℝ)*X 1 1+(4495134811/10000000000 : ℝ)*X 1 2+(545831479/1250000000 : ℝ)*X 2 0+(4241836123/10000000000 : ℝ)*X 2 1+(4495134811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1086805319/5000000000 : ℝ)*X 0 0+(5265881247/10000000000 : ℝ)*X 0 1+(5392909409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((34114543/78125000 : ℝ)*X 0 0+(898899867/2000000000 : ℝ)*X 0 1+(4242473951/10000000000 : ℝ)*X 0 2+(34114543/78125000 : ℝ)*X 1 0+(898899867/2000000000 : ℝ)*X 1 1+(4242473951/10000000000 : ℝ)*X 1 2+(34114543/78125000 : ℝ)*X 2 0+(898899867/2000000000 : ℝ)*X 2 1+(4242473951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23692205112380099175969879/6762500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86897913/10000000000000 : ℝ)*(base19) + (684528469/100000000000000 : ℝ)*(base23) + (919643/4000000000000 : ℝ)*(lower2) + (157282443/100000000000000 : ℝ)*(upper3) + (1016643/20000000000000 : ℝ)*(lower4) + (5890333975234927/100000000000000 : ℝ)*(major0) + (5890333975234927/100000000000000 : ℝ)*(major1) + (5890333975234927/100000000000000 : ℝ)*(major2) + (7832723732946023/100000000000000 : ℝ)*(sp0) + (979092306567021/12500000000000 : ℝ)*(sp1) + (7832738636986829/100000000000000 : ℝ)*(sp2) + (197395855352821/5000000000000 : ℝ)*(sp3) + (623542771/4000000000000 : ℝ)*(sp4) + (35640987/312500000000 : ℝ)*(sp5) + (3947928512172259/100000000000000 : ℝ)*(f.failure) + (3916369660757649/50000000000000 : ℝ)*(f.sum) + (87358391132573/6762500000000000000000000000 : ℝ)*base66 + (277360254951416207/27050000000000000000000000000000 : ℝ)*base68 + (166180404368983793/27050000000000000000000000000000 : ℝ)*base69 + (561092511087216207/27050000000000000000000000000000 : ℝ)*base72 + (210209407439/211328125000000000000000000 : ℝ)*base74 + (327727589312616207/27050000000000000000000000000000 : ℝ)*base76 + (510839073699466207/27050000000000000000000000000000 : ℝ)*base78 + (1089567969998316207/27050000000000000000000000000000 : ℝ)*base80 + (1683626334347/422656250000000000000000000 : ℝ)*base81 + (3856899/625000000000000000000 : ℝ)*base90 + (3856899/625000000000000000000 : ℝ)*base92 + (3856899/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1128_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (351/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1128_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1128_box_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2046248573/10000000000 : ℝ)*x 0 + (1344126827/2500000000 : ℝ)*x 1 + (672063411/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046248573/10000000000 : ℝ)^8321 ≤ (12189926234309/100000000000000 : ℝ)^6273 := by
    have hnat : (2046248573 : ℕ)^8321*100000000000000^6273 ≤ 12189926234309^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046248573 10000000000 12189926234309 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344126827/2500000000 : ℝ)^8321 ≤ (5488129623103/12500000000000 : ℝ)^6273 := by
    have hnat : (1344126827 : ℕ)^8321*12500000000000^6273 ≤ 5488129623103^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344126827 2500000000 5488129623103 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672063411/1250000000 : ℝ)^8321 ≤ (21952518384091/50000000000000 : ℝ)^6273 := by
    have hnat : (672063411 : ℕ)^8321*50000000000000^6273 ≤ 21952518384091^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672063411 1250000000 21952518384091 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2046248573/10000000000 : ℝ), (1344126827/2500000000 : ℝ), (672063411/1250000000 : ℝ)] ![(12189926234309/100000000000000 : ℝ), (5488129623103/12500000000000 : ℝ), (21952518384091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2046248573/10000000000 : ℝ)|^8321 ≤ (12189926234309/100000000000000 : ℝ)^6273
        have hw : |(-2046248573/10000000000 : ℝ)|=(2046248573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344126827/2500000000 : ℝ)|^8321 ≤ (5488129623103/12500000000000 : ℝ)^6273
        have hw : |(1344126827/2500000000 : ℝ)|=(1344126827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672063411/1250000000 : ℝ)|^8321 ≤ (21952518384091/50000000000000 : ℝ)^6273
        have hw : |(672063411/1250000000 : ℝ)|=(672063411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1059170669/2000000000 : ℝ)*x 0 + (-215559419/1000000000 : ℝ)*x 1 + (5376507191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059170669/2000000000 : ℝ)^8321 ≤ (43033528453213/100000000000000 : ℝ)^6273 := by
    have hnat : (1059170669 : ℕ)^8321*100000000000000^6273 ≤ 43033528453213^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059170669 2000000000 43033528453213 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215559419/1000000000 : ℝ)^8321 ≤ (6530717903631/50000000000000 : ℝ)^6273 := by
    have hnat : (215559419 : ℕ)^8321*50000000000000^6273 ≤ 6530717903631^6273*1000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215559419 1000000000 6530717903631 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376507191/10000000000 : ℝ)^8321 ≤ (5488129464683/12500000000000 : ℝ)^6273 := by
    have hnat : (5376507191 : ℕ)^8321*12500000000000^6273 ≤ 5488129464683^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376507191 10000000000 5488129464683 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059170669/2000000000 : ℝ), (-215559419/1000000000 : ℝ), (5376507191/10000000000 : ℝ)] ![(43033528453213/100000000000000 : ℝ), (6530717903631/50000000000000 : ℝ), (5488129464683/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059170669/2000000000 : ℝ)|^8321 ≤ (43033528453213/100000000000000 : ℝ)^6273
        have hw : |(1059170669/2000000000 : ℝ)|=(1059170669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215559419/1000000000 : ℝ)|^8321 ≤ (6530717903631/50000000000000 : ℝ)^6273
        have hw : |(-215559419/1000000000 : ℝ)|=(215559419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376507191/10000000000 : ℝ)|^8321 ≤ (5488129464683/12500000000000 : ℝ)^6273
        have hw : |(5376507191/10000000000 : ℝ)|=(5376507191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295853233/10000000000 : ℝ)*x 0 + (5376507367/10000000000 : ℝ)*x 1 + (-431118821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295853233/10000000000 : ℝ)^8321 ≤ (8606705449197/20000000000000 : ℝ)^6273 := by
    have hnat : (5295853233 : ℕ)^8321*20000000000000^6273 ≤ 8606705449197^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295853233 10000000000 8606705449197 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376507367/10000000000 : ℝ)^8321 ≤ (43905037623921/100000000000000 : ℝ)^6273 := by
    have hnat : (5376507367 : ℕ)^8321*100000000000000^6273 ≤ 43905037623921^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376507367 10000000000 43905037623921 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (431118821/2000000000 : ℝ)^8321 ≤ (1306143512407/10000000000000 : ℝ)^6273 := by
    have hnat : (431118821 : ℕ)^8321*10000000000000^6273 ≤ 1306143512407^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431118821 2000000000 1306143512407 10000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295853233/10000000000 : ℝ), (5376507367/10000000000 : ℝ), (-431118821/2000000000 : ℝ)] ![(8606705449197/20000000000000 : ℝ), (43905037623921/100000000000000 : ℝ), (1306143512407/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295853233/10000000000 : ℝ)|^8321 ≤ (8606705449197/20000000000000 : ℝ)^6273
        have hw : |(5295853233/10000000000 : ℝ)|=(5295853233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376507367/10000000000 : ℝ)|^8321 ≤ (43905037623921/100000000000000 : ℝ)^6273
        have hw : |(5376507367/10000000000 : ℝ)|=(5376507367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-431118821/2000000000 : ℝ)|^8321 ≤ (1306143512407/10000000000000 : ℝ)^6273
        have hw : |(-431118821/2000000000 : ℝ)|=(431118821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4474343641/10000000000 : ℝ)*x 0 + (2157461657/5000000000 : ℝ)*x 1 + (43149233/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4474343641/10000000000 : ℝ)^8321 ≤ (17205605353977/50000000000000 : ℝ)^6273 := by
    have hnat : (4474343641 : ℕ)^8321*50000000000000^6273 ≤ 17205605353977^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474343641 10000000000 17205605353977 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2157461657/5000000000 : ℝ)^8321 ≤ (3279439470927/10000000000000 : ℝ)^6273 := by
    have hnat : (2157461657 : ℕ)^8321*10000000000000^6273 ≤ 3279439470927^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157461657 5000000000 3279439470927 10000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43149233/100000000 : ℝ)^8321 ≤ (32794394568129/100000000000000 : ℝ)^6273 := by
    have hnat : (43149233 : ℕ)^8321*100000000000000^6273 ≤ 32794394568129^6273*100000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43149233 100000000 32794394568129 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4474343641/10000000000 : ℝ), (2157461657/5000000000 : ℝ), (43149233/100000000 : ℝ)] ![(17205605353977/50000000000000 : ℝ), (3279439470927/10000000000000 : ℝ), (32794394568129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4474343641/10000000000 : ℝ)|^8321 ≤ (17205605353977/50000000000000 : ℝ)^6273
        have hw : |(4474343641/10000000000 : ℝ)|=(4474343641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2157461657/5000000000 : ℝ)|^8321 ≤ (3279439470927/10000000000000 : ℝ)^6273
        have hw : |(2157461657/5000000000 : ℝ)|=(2157461657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43149233/100000000 : ℝ)|^8321 ≤ (32794394568129/100000000000000 : ℝ)^6273
        have hw : |(43149233/100000000 : ℝ)|=(43149233/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-92093623/400000000 : ℝ)*x 0 + (211238473/400000000 : ℝ)*x 1 + (1056192191/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92093623/400000000 : ℝ)^8321 ≤ (14253831049479/100000000000000 : ℝ)^6273 := by
    have hnat : (92093623 : ℕ)^8321*100000000000000^6273 ≤ 14253831049479^6273*400000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92093623 400000000 14253831049479 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211238473/400000000 : ℝ)^8321 ≤ (42873089156179/100000000000000 : ℝ)^6273 := by
    have hnat : (211238473 : ℕ)^8321*100000000000000^6273 ≤ 42873089156179^6273*400000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211238473 400000000 42873089156179 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056192191/2000000000 : ℝ)^8321 ≤ (21436539893611/50000000000000 : ℝ)^6273 := by
    have hnat : (1056192191 : ℕ)^8321*50000000000000^6273 ≤ 21436539893611^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056192191 2000000000 21436539893611 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-92093623/400000000 : ℝ), (211238473/400000000 : ℝ), (1056192191/2000000000 : ℝ)] ![(14253831049479/100000000000000 : ℝ), (42873089156179/100000000000000 : ℝ), (21436539893611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-92093623/400000000 : ℝ)|^8321 ≤ (14253831049479/100000000000000 : ℝ)^6273
        have hw : |(-92093623/400000000 : ℝ)|=(92093623/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211238473/400000000 : ℝ)|^8321 ≤ (42873089156179/100000000000000 : ℝ)^6273
        have hw : |(211238473/400000000 : ℝ)|=(211238473/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056192191/2000000000 : ℝ)|^8321 ≤ (21436539893611/50000000000000 : ℝ)^6273
        have hw : |(1056192191/2000000000 : ℝ)|=(1056192191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_5 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681688771/5000000000 : ℝ)*x 0 + (-548284217/2500000000 : ℝ)*x 1 + (528096171/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681688771/5000000000 : ℝ)^8321 ≤ (43762870223309/100000000000000 : ℝ)^6273 := by
    have hnat : (2681688771 : ℕ)^8321*100000000000000^6273 ≤ 43762870223309^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681688771 5000000000 43762870223309 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548284217/2500000000 : ℝ)^8321 ≤ (13364041841583/100000000000000 : ℝ)^6273 := by
    have hnat : (548284217 : ℕ)^8321*100000000000000^6273 ≤ 13364041841583^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548284217 2500000000 13364041841583 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528096171/1000000000 : ℝ)^8321 ≤ (42873087917753/100000000000000 : ℝ)^6273 := by
    have hnat : (528096171 : ℕ)^8321*100000000000000^6273 ≤ 42873087917753^6273*1000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528096171 1000000000 42873087917753 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681688771/5000000000 : ℝ), (-548284217/2500000000 : ℝ), (528096171/1000000000 : ℝ)] ![(43762870223309/100000000000000 : ℝ), (13364041841583/100000000000000 : ℝ), (42873087917753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681688771/5000000000 : ℝ)|^8321 ≤ (43762870223309/100000000000000 : ℝ)^6273
        have hw : |(2681688771/5000000000 : ℝ)|=(2681688771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-548284217/2500000000 : ℝ)|^8321 ≤ (13364041841583/100000000000000 : ℝ)^6273
        have hw : |(-548284217/2500000000 : ℝ)|=(548284217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528096171/1000000000 : ℝ)|^8321 ≤ (42873087917753/100000000000000 : ℝ)^6273
        have hw : |(528096171/1000000000 : ℝ)|=(528096171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1340844347/2500000000 : ℝ)*x 0 + (2640480879/5000000000 : ℝ)*x 1 + (-2193137011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340844347/2500000000 : ℝ)^8321 ≤ (4376286855649/10000000000000 : ℝ)^6273 := by
    have hnat : (1340844347 : ℕ)^8321*10000000000000^6273 ≤ 4376286855649^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340844347 2500000000 4376286855649 10000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640480879/5000000000 : ℝ)^8321 ≤ (42873088434661/100000000000000 : ℝ)^6273 := by
    have hnat : (2640480879 : ℕ)^8321*100000000000000^6273 ≤ 42873088434661^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640480879 5000000000 42873088434661 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2193137011/10000000000 : ℝ)^8321 ≤ (13364042997451/100000000000000 : ℝ)^6273 := by
    have hnat : (2193137011 : ℕ)^8321*100000000000000^6273 ≤ 13364042997451^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193137011 10000000000 13364042997451 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340844347/2500000000 : ℝ), (2640480879/5000000000 : ℝ), (-2193137011/10000000000 : ℝ)] ![(4376286855649/10000000000000 : ℝ), (42873088434661/100000000000000 : ℝ), (13364042997451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340844347/2500000000 : ℝ)|^8321 ≤ (4376286855649/10000000000000 : ℝ)^6273
        have hw : |(1340844347/2500000000 : ℝ)|=(1340844347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640480879/5000000000 : ℝ)|^8321 ≤ (42873088434661/100000000000000 : ℝ)^6273
        have hw : |(2640480879/5000000000 : ℝ)|=(2640480879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2193137011/10000000000 : ℝ)|^8321 ≤ (13364042997451/100000000000000 : ℝ)^6273
        have hw : |(-2193137011/10000000000 : ℝ)|=(2193137011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2129302021/5000000000 : ℝ)*x 0 + (1105693023/2500000000 : ℝ)*x 1 + (4422772221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129302021/5000000000 : ℝ)^8321 ≤ (16113911579527/50000000000000 : ℝ)^6273 := by
    have hnat : (2129302021 : ℕ)^8321*50000000000000^6273 ≤ 16113911579527^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129302021 5000000000 16113911579527 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105693023/2500000000 : ℝ)^8321 ≤ (16943043877513/50000000000000 : ℝ)^6273 := by
    have hnat : (1105693023 : ℕ)^8321*50000000000000^6273 ≤ 16943043877513^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105693023 2500000000 16943043877513 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4422772221/10000000000 : ℝ)^8321 ≤ (8471522266517/25000000000000 : ℝ)^6273 := by
    have hnat : (4422772221 : ℕ)^8321*25000000000000^6273 ≤ 8471522266517^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4422772221 10000000000 8471522266517 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2129302021/5000000000 : ℝ), (1105693023/2500000000 : ℝ), (4422772221/10000000000 : ℝ)] ![(16113911579527/50000000000000 : ℝ), (16943043877513/50000000000000 : ℝ), (8471522266517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2129302021/5000000000 : ℝ)|^8321 ≤ (16113911579527/50000000000000 : ℝ)^6273
        have hw : |(2129302021/5000000000 : ℝ)|=(2129302021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1105693023/2500000000 : ℝ)|^8321 ≤ (16943043877513/50000000000000 : ℝ)^6273
        have hw : |(1105693023/2500000000 : ℝ)|=(1105693023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4422772221/10000000000 : ℝ)|^8321 ≤ (8471522266517/25000000000000 : ℝ)^6273
        have hw : |(4422772221/10000000000 : ℝ)|=(4422772221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-449760797/2000000000 : ℝ)*x 0 + (2608003871/5000000000 : ℝ)*x 1 + (1346528649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449760797/2000000000 : ℝ)^8321 ≤ (863490795531/6250000000000 : ℝ)^6273 := by
    have hnat : (449760797 : ℕ)^8321*6250000000000^6273 ≤ 863490795531^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449760797 2000000000 863490795531 6250000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608003871/5000000000 : ℝ)^8321 ≤ (10543753104671/25000000000000 : ℝ)^6273 := by
    have hnat : (2608003871 : ℕ)^8321*25000000000000^6273 ≤ 10543753104671^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608003871 5000000000 10543753104671 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346528649/2500000000 : ℝ)^8321 ≤ (44009134835437/100000000000000 : ℝ)^6273 := by
    have hnat : (1346528649 : ℕ)^8321*100000000000000^6273 ≤ 44009134835437^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346528649 2500000000 44009134835437 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-449760797/2000000000 : ℝ), (2608003871/5000000000 : ℝ), (1346528649/2500000000 : ℝ)] ![(863490795531/6250000000000 : ℝ), (10543753104671/25000000000000 : ℝ), (44009134835437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-449760797/2000000000 : ℝ)|^8321 ≤ (863490795531/6250000000000 : ℝ)^6273
        have hw : |(-449760797/2000000000 : ℝ)|=(449760797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608003871/5000000000 : ℝ)|^8321 ≤ (10543753104671/25000000000000 : ℝ)^6273
        have hw : |(2608003871/5000000000 : ℝ)|=(2608003871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346528649/2500000000 : ℝ)|^8321 ≤ (44009134835437/100000000000000 : ℝ)^6273
        have hw : |(1346528649/2500000000 : ℝ)|=(1346528649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289060109/10000000000 : ℝ)*x 0 + (-67242181/312500000 : ℝ)*x 1 + (2693057261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289060109/10000000000 : ℝ)^8321 ≤ (42960320718421/100000000000000 : ℝ)^6273 := by
    have hnat : (5289060109 : ℕ)^8321*100000000000000^6273 ≤ 42960320718421^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289060109 10000000000 42960320718421 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67242181/312500000 : ℝ)^8321 ≤ (3257636308141/25000000000000 : ℝ)^6273 := by
    have hnat : (67242181 : ℕ)^8321*25000000000000^6273 ≤ 3257636308141^6273*312500000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67242181 312500000 3257636308141 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693057261/5000000000 : ℝ)^8321 ≤ (44009134033391/100000000000000 : ℝ)^6273 := by
    have hnat : (2693057261 : ℕ)^8321*100000000000000^6273 ≤ 44009134033391^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693057261 5000000000 44009134033391 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289060109/10000000000 : ℝ), (-67242181/312500000 : ℝ), (2693057261/5000000000 : ℝ)] ![(42960320718421/100000000000000 : ℝ), (3257636308141/25000000000000 : ℝ), (44009134033391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289060109/10000000000 : ℝ)|^8321 ≤ (42960320718421/100000000000000 : ℝ)^6273
        have hw : |(5289060109/10000000000 : ℝ)|=(5289060109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67242181/312500000 : ℝ)|^8321 ≤ (3257636308141/25000000000000 : ℝ)^6273
        have hw : |(-67242181/312500000 : ℝ)|=(67242181/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693057261/5000000000 : ℝ)|^8321 ≤ (44009134033391/100000000000000 : ℝ)^6273
        have hw : |(2693057261/5000000000 : ℝ)|=(2693057261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_10 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (528906019/1000000000 : ℝ)*x 0 + (538611461/1000000000 : ℝ)*x 1 + (-537937391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528906019/1000000000 : ℝ)^8321 ≤ (2148016079557/5000000000000 : ℝ)^6273 := by
    have hnat : (528906019 : ℕ)^8321*5000000000000^6273 ≤ 2148016079557^6273*1000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528906019 1000000000 2148016079557 5000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538611461/1000000000 : ℝ)^8321 ≤ (1760365399487/4000000000000 : ℝ)^6273 := by
    have hnat : (538611461 : ℕ)^8321*4000000000000^6273 ≤ 1760365399487^6273*1000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538611461 1000000000 1760365399487 4000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537937391/2500000000 : ℝ)^8321 ≤ (3257635850267/25000000000000 : ℝ)^6273 := by
    have hnat : (537937391 : ℕ)^8321*25000000000000^6273 ≤ 3257635850267^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537937391 2500000000 3257635850267 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528906019/1000000000 : ℝ), (538611461/1000000000 : ℝ), (-537937391/2500000000 : ℝ)] ![(2148016079557/5000000000000 : ℝ), (1760365399487/4000000000000 : ℝ), (3257635850267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528906019/1000000000 : ℝ)|^8321 ≤ (2148016079557/5000000000000 : ℝ)^6273
        have hw : |(528906019/1000000000 : ℝ)|=(528906019/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538611461/1000000000 : ℝ)|^8321 ≤ (1760365399487/4000000000000 : ℝ)^6273
        have hw : |(538611461/1000000000 : ℝ)|=(538611461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-537937391/2500000000 : ℝ)|^8321 ≤ (3257635850267/25000000000000 : ℝ)^6273
        have hw : |(-537937391/2500000000 : ℝ)|=(537937391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_11 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (899152641/2000000000 : ℝ)*x 0 + (33625569/78125000 : ℝ)*x 1 + (4304073169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899152641/2000000000 : ℝ)^8321 ≤ (2164368524853/6250000000000 : ℝ)^6273 := by
    have hnat : (899152641 : ℕ)^8321*6250000000000^6273 ≤ 2164368524853^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899152641 2000000000 2164368524853 6250000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33625569/78125000 : ℝ)^8321 ≤ (4085631261999/12500000000000 : ℝ)^6273 := by
    have hnat : (33625569 : ℕ)^8321*12500000000000^6273 ≤ 4085631261999^6273*78125000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33625569 78125000 4085631261999 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4304073169/10000000000 : ℝ)^8321 ≤ (32685053490679/100000000000000 : ℝ)^6273 := by
    have hnat : (4304073169 : ℕ)^8321*100000000000000^6273 ≤ 32685053490679^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304073169 10000000000 32685053490679 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(899152641/2000000000 : ℝ), (33625569/78125000 : ℝ), (4304073169/10000000000 : ℝ)] ![(2164368524853/6250000000000 : ℝ), (4085631261999/12500000000000 : ℝ), (32685053490679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(899152641/2000000000 : ℝ)|^8321 ≤ (2164368524853/6250000000000 : ℝ)^6273
        have hw : |(899152641/2000000000 : ℝ)|=(899152641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33625569/78125000 : ℝ)|^8321 ≤ (4085631261999/12500000000000 : ℝ)^6273
        have hw : |(33625569/78125000 : ℝ)|=(33625569/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4304073169/10000000000 : ℝ)|^8321 ≤ (32685053490679/100000000000000 : ℝ)^6273
        have hw : |(4304073169/10000000000 : ℝ)|=(4304073169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_12 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2100112649/10000000000 : ℝ)*x 0 + (1088034613/2000000000 : ℝ)*x 1 + (131823241/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100112649/10000000000 : ℝ)^8321 ≤ (3154346056351/25000000000000 : ℝ)^6273 := by
    have hnat : (2100112649 : ℕ)^8321*25000000000000^6273 ≤ 3154346056351^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100112649 10000000000 3154346056351 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088034613/2000000000 : ℝ)^8321 ≤ (44596003036253/100000000000000 : ℝ)^6273 := by
    have hnat : (1088034613 : ℕ)^8321*100000000000000^6273 ≤ 44596003036253^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088034613 2000000000 44596003036253 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131823241/250000000 : ℝ)^8321 ≤ (21393306357507/50000000000000 : ℝ)^6273 := by
    have hnat : (131823241 : ℕ)^8321*50000000000000^6273 ≤ 21393306357507^6273*250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131823241 250000000 21393306357507 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2100112649/10000000000 : ℝ), (1088034613/2000000000 : ℝ), (131823241/250000000 : ℝ)] ![(3154346056351/25000000000000 : ℝ), (44596003036253/100000000000000 : ℝ), (21393306357507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2100112649/10000000000 : ℝ)|^8321 ≤ (3154346056351/25000000000000 : ℝ)^6273
        have hw : |(-2100112649/10000000000 : ℝ)|=(2100112649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088034613/2000000000 : ℝ)|^8321 ≤ (44596003036253/100000000000000 : ℝ)^6273
        have hw : |(1088034613/2000000000 : ℝ)|=(1088034613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131823241/250000000 : ℝ)|^8321 ≤ (21393306357507/50000000000000 : ℝ)^6273
        have hw : |(131823241/250000000 : ℝ)|=(131823241/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369051701/10000000000 : ℝ)*x 0 + (-1098117413/5000000000 : ℝ)*x 1 + (5272929993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369051701/10000000000 : ℝ)^8321 ≤ (43824295078607/100000000000000 : ℝ)^6273 := by
    have hnat : (5369051701 : ℕ)^8321*100000000000000^6273 ≤ 43824295078607^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369051701 10000000000 43824295078607 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098117413/5000000000 : ℝ)^8321 ≤ (13389088393733/100000000000000 : ℝ)^6273 := by
    have hnat : (1098117413 : ℕ)^8321*100000000000000^6273 ≤ 13389088393733^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098117413 5000000000 13389088393733 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272929993/10000000000 : ℝ)^8321 ≤ (42786616514553/100000000000000 : ℝ)^6273 := by
    have hnat : (5272929993 : ℕ)^8321*100000000000000^6273 ≤ 42786616514553^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272929993 10000000000 42786616514553 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369051701/10000000000 : ℝ), (-1098117413/5000000000 : ℝ), (5272929993/10000000000 : ℝ)] ![(43824295078607/100000000000000 : ℝ), (13389088393733/100000000000000 : ℝ), (42786616514553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369051701/10000000000 : ℝ)|^8321 ≤ (43824295078607/100000000000000 : ℝ)^6273
        have hw : |(5369051701/10000000000 : ℝ)|=(5369051701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1098117413/5000000000 : ℝ)|^8321 ≤ (13389088393733/100000000000000 : ℝ)^6273
        have hw : |(-1098117413/5000000000 : ℝ)|=(1098117413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272929993/10000000000 : ℝ)|^8321 ≤ (42786616514553/100000000000000 : ℝ)^6273
        have hw : |(5272929993/10000000000 : ℝ)|=(5272929993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369051703/10000000000 : ℝ)*x 0 + (1318232407/2500000000 : ℝ)*x 1 + (-2196235309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369051703/10000000000 : ℝ)^8321 ≤ (21912147550131/50000000000000 : ℝ)^6273 := by
    have hnat : (5369051703 : ℕ)^8321*50000000000000^6273 ≤ 21912147550131^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369051703 10000000000 21912147550131 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318232407/2500000000 : ℝ)^8321 ≤ (42786612585851/100000000000000 : ℝ)^6273 := by
    have hnat : (1318232407 : ℕ)^8321*100000000000000^6273 ≤ 42786612585851^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318232407 2500000000 42786612585851 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196235309/10000000000 : ℝ)^8321 ≤ (669454614981/5000000000000 : ℝ)^6273 := by
    have hnat : (2196235309 : ℕ)^8321*5000000000000^6273 ≤ 669454614981^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196235309 10000000000 669454614981 5000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369051703/10000000000 : ℝ), (1318232407/2500000000 : ℝ), (-2196235309/10000000000 : ℝ)] ![(21912147550131/50000000000000 : ℝ), (42786612585851/100000000000000 : ℝ), (669454614981/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369051703/10000000000 : ℝ)|^8321 ≤ (21912147550131/50000000000000 : ℝ)^6273
        have hw : |(5369051703/10000000000 : ℝ)|=(5369051703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1318232407/2500000000 : ℝ)|^8321 ≤ (42786612585851/100000000000000 : ℝ)^6273
        have hw : |(1318232407/2500000000 : ℝ)|=(1318232407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196235309/10000000000 : ℝ)|^8321 ≤ (669454614981/5000000000000 : ℝ)^6273
        have hw : |(-2196235309/10000000000 : ℝ)|=(2196235309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_box_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530029723/1250000000 : ℝ)*x 0 + (1107958201/2500000000 : ℝ)*x 1 + (2215916757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530029723/1250000000 : ℝ)^8321 ≤ (16021792735829/50000000000000 : ℝ)^6273 := by
    have hnat : (530029723 : ℕ)^8321*50000000000000^6273 ≤ 16021792735829^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530029723 1250000000 16021792735829 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107958201/2500000000 : ℝ)^8321 ≤ (3397820365029/10000000000000 : ℝ)^6273 := by
    have hnat : (1107958201 : ℕ)^8321*10000000000000^6273 ≤ 3397820365029^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107958201 2500000000 3397820365029 10000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2215916757/5000000000 : ℝ)^8321 ≤ (33978210870929/100000000000000 : ℝ)^6273 := by
    have hnat : (2215916757 : ℕ)^8321*100000000000000^6273 ≤ 33978210870929^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215916757 5000000000 33978210870929 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530029723/1250000000 : ℝ), (1107958201/2500000000 : ℝ), (2215916757/5000000000 : ℝ)] ![(16021792735829/50000000000000 : ℝ), (3397820365029/10000000000000 : ℝ), (33978210870929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530029723/1250000000 : ℝ)|^8321 ≤ (16021792735829/50000000000000 : ℝ)^6273
        have hw : |(530029723/1250000000 : ℝ)|=(530029723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1107958201/2500000000 : ℝ)|^8321 ≤ (3397820365029/10000000000000 : ℝ)^6273
        have hw : |(1107958201/2500000000 : ℝ)|=(1107958201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2215916757/5000000000 : ℝ)|^8321 ≤ (33978210870929/100000000000000 : ℝ)^6273
        have hw : |(2215916757/5000000000 : ℝ)|=(2215916757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1128_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(62229/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7411/12500 : ℝ) ∧ (15953/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83093/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (351/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1417/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (351/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1417/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (351/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1417/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (351/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1417/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (351/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1417/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (351/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1417/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1417/12500 : ℝ) ^ (65/16 : ℝ) ≤ (7206312530712907/50000000000000000000 : ℝ) := by
    have hpowers : (1417/12500 : ℝ)^65 ≤ (7206312530712907/50000000000000000000 : ℝ)^16 := by
      have hnat : (1417 : ℕ)^65*50000000000000000000^16 ≤ 7206312530712907^16*12500^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1417 12500 7206312530712907 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1417/12500 : ℝ)) (X := (7206312530712907/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hpowhi : (351/2500 : ℝ) ^ (65/16 : ℝ) ≤ (34369948026924089/100000000000000000000 : ℝ) := by
    have hpowers : (351/2500 : ℝ)^65 ≤ (34369948026924089/100000000000000000000 : ℝ)^16 := by
      have hnat : (351 : ℕ)^65*100000000000000000000^16 ≤ 34369948026924089^16*2500^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        351 2500 34369948026924089 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (351/2500 : ℝ)) (X := (34369948026924089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007206312530712907/25000000000000000000 : ℝ) ≤ (10000709467540071/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (25007206312530712907/25000000000000000000 : ℝ)^16 ≤ (10000709467540071/10000000000000000 : ℝ)^65 := by
      have hnat : (25007206312530712907 : ℕ)^16*10000000000000000^65 ≤ 10000709467540071^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007206312530712907 25000000000000000000 10000709467540071 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000709467540071/10000000000000000 : ℝ)) (X := (25007206312530712907/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048782573088349903/100000000000000000000 : ℝ) ≤ (5000600290533643/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (100048782573088349903/100000000000000000000 : ℝ)^16 ≤ (5000600290533643/5000000000000000 : ℝ)^65 := by
      have hnat : (100048782573088349903 : ℕ)^16*5000000000000000^65 ≤ 5000600290533643^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048782573088349903 100000000000000000000 5000600290533643 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000600290533643/5000000000000000 : ℝ)) (X := (100048782573088349903/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034369948026924089/50000000000000000000 : ℝ) ≤ (10001691694594501/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50034369948026924089/50000000000000000000 : ℝ)^16 ≤ (10001691694594501/10000000000000000 : ℝ)^65 := by
      have hnat : (50034369948026924089 : ℕ)^16*10000000000000000^65 ≤ 10001691694594501^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034369948026924089 50000000000000000000 10001691694594501 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001691694594501/10000000000000000 : ℝ)) (X := (50034369948026924089/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7206312530712907/50000000000000000000 : ℝ) ≤ ((16244461462944311/16250000000000000 : ℝ)+2*(98222705443/54080000000000 : ℝ)*(1417/12500 : ℝ))^(65/16 : ℝ) := by
    rw [show (16244461462944311/16250000000000000 : ℝ)+2*(98222705443/54080000000000 : ℝ)*(1417/12500 : ℝ)=(10000709467540071/10000000000000000 : ℝ) by norm_num, show 1+2*(7206312530712907/50000000000000000000 : ℝ)=(25007206312530712907/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34369948026924089/100000000000000000000 : ℝ)+(7206312530712907/50000000000000000000 : ℝ) ≤ ((16244461462944311/16250000000000000 : ℝ)+(98222705443/54080000000000 : ℝ)*((351/2500 : ℝ)+(1417/12500 : ℝ)))^(65/16 : ℝ) := by
    rw [show (16244461462944311/16250000000000000 : ℝ)+(98222705443/54080000000000 : ℝ)*((351/2500 : ℝ)+(1417/12500 : ℝ))=(5000600290533643/5000000000000000 : ℝ) by norm_num, show 1+(34369948026924089/100000000000000000000 : ℝ)+(7206312530712907/50000000000000000000 : ℝ)=(100048782573088349903/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34369948026924089/100000000000000000000 : ℝ) ≤ ((16244461462944311/16250000000000000 : ℝ)+2*(98222705443/54080000000000 : ℝ)*(351/2500 : ℝ))^(65/16 : ℝ) := by
    rw [show (16244461462944311/16250000000000000 : ℝ)+2*(98222705443/54080000000000 : ℝ)*(351/2500 : ℝ)=(10001691694594501/10000000000000000 : ℝ) by norm_num, show 1+2*(34369948026924089/100000000000000000000 : ℝ)=(50034369948026924089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16244461462944311/16250000000000000 : ℝ)*(X 1 0+X 2 0)+(98222705443/54080000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (1417/12500 : ℝ)) (hi := (351/2500 : ℝ)) (c := (16244461462944311/16250000000000000 : ℝ)) (alpha := (98222705443/54080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16244461462944311/16250000000000000 : ℝ)*(X 0 1+X 2 1)+(98222705443/54080000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (1417/12500 : ℝ)) (hi := (351/2500 : ℝ)) (c := (16244461462944311/16250000000000000 : ℝ)) (alpha := (98222705443/54080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16244461462944311/16250000000000000 : ℝ)*(X 0 2+X 1 2)+(98222705443/54080000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (1417/12500 : ℝ)) (hi := (351/2500 : ℝ)) (c := (16244461462944311/16250000000000000 : ℝ)) (alpha := (98222705443/54080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2046248573/10000000000 : ℝ)*X 0 0+(1344126827/2500000000 : ℝ)*X 0 1+(672063411/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1059170669/2000000000 : ℝ)*X 1 0+(-215559419/1000000000 : ℝ)*X 1 1+(5376507191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295853233/10000000000 : ℝ)*X 2 0+(5376507367/10000000000 : ℝ)*X 2 1+(-431118821/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4474343641/10000000000 : ℝ)*X 0 0+(2157461657/5000000000 : ℝ)*X 0 1+(43149233/100000000 : ℝ)*X 0 2+(4474343641/10000000000 : ℝ)*X 1 0+(2157461657/5000000000 : ℝ)*X 1 1+(43149233/100000000 : ℝ)*X 1 2+(4474343641/10000000000 : ℝ)*X 2 0+(2157461657/5000000000 : ℝ)*X 2 1+(43149233/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-92093623/400000000 : ℝ)*X 0 0+(211238473/400000000 : ℝ)*X 0 1+(1056192191/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681688771/5000000000 : ℝ)*X 1 0+(-548284217/2500000000 : ℝ)*X 1 1+(528096171/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1340844347/2500000000 : ℝ)*X 2 0+(2640480879/5000000000 : ℝ)*X 2 1+(-2193137011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2129302021/5000000000 : ℝ)*X 0 0+(1105693023/2500000000 : ℝ)*X 0 1+(4422772221/10000000000 : ℝ)*X 0 2+(2129302021/5000000000 : ℝ)*X 1 0+(1105693023/2500000000 : ℝ)*X 1 1+(4422772221/10000000000 : ℝ)*X 1 2+(2129302021/5000000000 : ℝ)*X 2 0+(1105693023/2500000000 : ℝ)*X 2 1+(4422772221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-449760797/2000000000 : ℝ)*X 0 0+(2608003871/5000000000 : ℝ)*X 0 1+(1346528649/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289060109/10000000000 : ℝ)*X 1 0+(-67242181/312500000 : ℝ)*X 1 1+(2693057261/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((528906019/1000000000 : ℝ)*X 2 0+(538611461/1000000000 : ℝ)*X 2 1+(-537937391/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((899152641/2000000000 : ℝ)*X 0 0+(33625569/78125000 : ℝ)*X 0 1+(4304073169/10000000000 : ℝ)*X 0 2+(899152641/2000000000 : ℝ)*X 1 0+(33625569/78125000 : ℝ)*X 1 1+(4304073169/10000000000 : ℝ)*X 1 2+(899152641/2000000000 : ℝ)*X 2 0+(33625569/78125000 : ℝ)*X 2 1+(4304073169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2100112649/10000000000 : ℝ)*X 0 0+(1088034613/2000000000 : ℝ)*X 0 1+(131823241/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369051701/10000000000 : ℝ)*X 1 0+(-1098117413/5000000000 : ℝ)*X 1 1+(5272929993/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369051703/10000000000 : ℝ)*X 2 0+(1318232407/2500000000 : ℝ)*X 2 1+(-2196235309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((530029723/1250000000 : ℝ)*X 0 0+(1107958201/2500000000 : ℝ)*X 0 1+(2215916757/5000000000 : ℝ)*X 0 2+(530029723/1250000000 : ℝ)*X 1 0+(1107958201/2500000000 : ℝ)*X 1 1+(2215916757/5000000000 : ℝ)*X 1 2+(530029723/1250000000 : ℝ)*X 2 0+(1107958201/2500000000 : ℝ)*X 2 1+(2215916757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62229/100000 : ℝ) ≤ (-2629089437804943128493770750577/4225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12546349/50000000000000 : ℝ)*(upper3) + (3042263/3125000000000 : ℝ)*(lower4) + (808493/12500000000000 : ℝ)*(lower5) + (781784016455623/20000000000000 : ℝ)*(major0) + (781784016455623/20000000000000 : ℝ)*(major1) + (781784016455623/20000000000000 : ℝ)*(major2) + (2337078069/25000000000000 : ℝ)*(sp3) + (1043730373853101/20000000000000 : ℝ)*(sp4) + (1043700372098349/20000000000000 : ℝ)*(sp5) + (326158237378957/6250000000000 : ℝ)*(sp6) + (1309949660310357/50000000000000 : ℝ)*(sp7) + (21949338439/100000000000000 : ℝ)*(sp8) + (171958112199/100000000000000 : ℝ)*(sp13) + (17752567579/12500000000000 : ℝ)*(sp14) + (261990866893299/10000000000000 : ℝ)*(f.failure) + (652334227325493/12500000000000 : ℝ)*(f.sum) + (1231712300311/2704000000000000000000000000 : ℝ)*base66 + (96468622435487281/16900000000000000000000000000000 : ℝ)*base67 + (222369029049287281/16900000000000000000000000000000 : ℝ)*base69 + (210954351957287281/16900000000000000000000000000000 : ℝ)*base71 + (5522422755927/2704000000000000000000000000 : ℝ)*base74 + (127606408767087281/16900000000000000000000000000000 : ℝ)*base75 + (109650782292587281/16900000000000000000000000000000 : ℝ)*base77 + (98345772545387281/16900000000000000000000000000000 : ℝ)*base79 + (491052716649/2704000000000000000000000000 : ℝ)*base81 + (138661/62500000000000000000 : ℝ)*base89 + (138661/62500000000000000000 : ℝ)*base91 + (138661/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (7411/12500 : ℝ) ≤ (12525057569441547602203372174719/21125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12252991/100000000000000 : ℝ)*(upper0) + (35745449/100000000000000 : ℝ)*(upper3) + (18185283/100000000000000 : ℝ)*(upper4) + (2100731/10000000000000 : ℝ)*(upper5) + (1986420980451083/50000000000000 : ℝ)*(major0) + (1986420980451083/50000000000000 : ℝ)*(major1) + (1986420980451083/50000000000000 : ℝ)*(major2) + (5263168945416921/100000000000000 : ℝ)*(sp0) + (5263078599630001/100000000000000 : ℝ)*(sp1) + (2631583305811203/50000000000000 : ℝ)*(sp2) + (1331374729141019/50000000000000 : ℝ)*(sp3) + (466758903/20000000000000 : ℝ)*(sp6) + (2113656539/100000000000000 : ℝ)*(sp7) + (2258644673/2500000000000 : ℝ)*(sp9) + (2662751571938577/100000000000000 : ℝ)*(f.failure) + (5263168945416921/100000000000000 : ℝ)*(f.sum) + (3269711754807/1352000000000000000000000000 : ℝ)*base66 + (281401432428233901/42250000000000000000000000000000 : ℝ)*base67 + (232332004465483901/42250000000000000000000000000000 : ℝ)*base69 + (7130215633983901/42250000000000000000000000000000 : ℝ)*base71 + (41324816555889/1352000000000000000000000000 : ℝ)*base73 + (160909681483733901/42250000000000000000000000000000 : ℝ)*base75 + (112673368620266099/42250000000000000000000000000000 : ℝ)*base78 + (1989861990934233901/42250000000000000000000000000000 : ℝ)*base79 + (815450937921/1352000000000000000000000000 : ℝ)*base81 + (1370497/625000000000000000000 : ℝ)*base90 + (1370497/625000000000000000000 : ℝ)*base92 + (1370497/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (15953/20000 : ℝ) ≤ (2106367721773801758595371766473/2640625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18876847/20000000000000 : ℝ)*(upper0) + (55517197/50000000000000 : ℝ)*(lower3) + (49354271/50000000000000 : ℝ)*(upper4) + (1110208802994721/25000000000000 : ℝ)*(major0) + (1110208802994721/25000000000000 : ℝ)*(major1) + (1110208802994721/25000000000000 : ℝ)*(major2) + (96875988643/100000000000000 : ℝ)*(sp1) + (43022516033/25000000000000 : ℝ)*(sp2) + (69506114191/100000000000000 : ℝ)*(sp3) + (2428796359/100000000000000 : ℝ)*(sp4) + (5878660078992073/100000000000000 : ℝ)*(sp8) + (1469641407949947/25000000000000 : ℝ)*(sp9) + (5878490417724299/100000000000000 : ℝ)*(sp10) + (2976349152817747/100000000000000 : ℝ)*(sp11) + (1488209329465969/50000000000000 : ℝ)*(f.failure) + (367416406736777/6250000000000 : ℝ)*(f.sum) + (1831412149133/676000000000000000000000000 : ℝ)*base66 + (61052132997747887/21125000000000000000000000000000 : ℝ)*base67 + (285321088621122887/21125000000000000000000000000000 : ℝ)*base69 + (173648309609497887/21125000000000000000000000000000 : ℝ)*base71 + (3738598703091/676000000000000000000000000 : ℝ)*base73 + (272891290805622887/21125000000000000000000000000000 : ℝ)*base75 + (277856290260622887/21125000000000000000000000000000 : ℝ)*base77 + (988571780583122887/21125000000000000000000000000000 : ℝ)*base79 + (1758721226631/676000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2402209/312500000000000000000 : ℝ)*base90 + (2402209/312500000000000000000 : ℝ)*base92 + (2402209/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-83093/100000 : ℝ) ≤ (-35105734304272973871195568521897/42250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54267213/100000000000000 : ℝ)*(lower0) + (64099117/50000000000000 : ℝ)*(lower1) + (34135051/12500000000000 : ℝ)*(lower4) + (4475731248578321/100000000000000 : ℝ)*(major0) + (4475731248578321/100000000000000 : ℝ)*(major1) + (4475731248578321/100000000000000 : ℝ)*(major2) + (16740406277/100000000000000 : ℝ)*(sp4) + (12084114033/2500000000000 : ℝ)*(sp6) + (114823449253/50000000000000 : ℝ)*(sp7) + (6134043457/100000000000000 : ℝ)*(sp8) + (5979329128914917/100000000000000 : ℝ)*(sp12) + (1494838000841163/25000000000000 : ℝ)*(sp13) + (5978868638803331/100000000000000 : ℝ)*(sp14) + (749894419672929/25000000000000 : ℝ)*(sp15) + (149990366279511/5000000000000 : ℝ)*(f.failure) + (1494838000841163/25000000000000 : ℝ)*(f.sum) + (16469486447069/2704000000000000000000000000 : ℝ)*base66 + (68882640235152087/84500000000000000000000000000000 : ℝ)*base67 + (52553167588652087/84500000000000000000000000000000 : ℝ)*base69 + (521772625159152087/84500000000000000000000000000000 : ℝ)*base71 + (19322705747/2704000000000000000000000000 : ℝ)*base73 + (592980750251847913/84500000000000000000000000000000 : ℝ)*base76 + (701657762974652087/84500000000000000000000000000000 : ℝ)*base77 + (202640968497152087/84500000000000000000000000000000 : ℝ)*base79 + (12150752308701/2704000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (336571/31250000000000000000 : ℝ)*base90 + (336571/31250000000000000000 : ℝ)*base92 + (336571/31250000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1128_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7411/12500 : ℝ) else (15953/20000 : ℝ) ≤ X j i ∧ X j i ≤ (83093/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1128_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1128_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7411/12500 : ℝ) else (15953/20000 : ℝ) ≤ X j i ∧ X j i ≤ (83093/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1128_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1128_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7411/12500 : ℝ) else (15953/20000 : ℝ) ≤ X j i ∧ X j i ≤ (83093/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1128_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
