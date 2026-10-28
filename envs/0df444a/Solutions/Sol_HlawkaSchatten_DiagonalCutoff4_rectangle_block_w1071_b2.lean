-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1071_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:10:59.667591+00:00
-- url     : https://prove2.me/submissions/62fe568c-74d3-4224-9327-47fd0ffe210b

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
theorem support_rectangle_w1071_s6_0 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1100631753/5000000000 : ℝ)*x 0 + (1078963003/2000000000 : ℝ)*x 1 + (5264028507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100631753/5000000000 : ℝ)^1033 ≤ (13369053379187/100000000000000 : ℝ)^777 := by
    have hnat : (1100631753 : ℕ)^1033*100000000000000^777 ≤ 13369053379187^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100631753 5000000000 13369053379187 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078963003/2000000000 : ℝ)^1033 ≤ (22011024336953/50000000000000 : ℝ)^777 := by
    have hnat : (1078963003 : ℕ)^1033*50000000000000^777 ≤ 22011024336953^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078963003 2000000000 22011024336953 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264028507/10000000000 : ℝ)^1033 ≤ (10652224481897/25000000000000 : ℝ)^777 := by
    have hnat : (5264028507 : ℕ)^1033*25000000000000^777 ≤ 10652224481897^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264028507 10000000000 10652224481897 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1100631753/5000000000 : ℝ), (1078963003/2000000000 : ℝ), (5264028507/10000000000 : ℝ)] ![(13369053379187/100000000000000 : ℝ), (22011024336953/50000000000000 : ℝ), (10652224481897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1100631753/5000000000 : ℝ)|^1033 ≤ (13369053379187/100000000000000 : ℝ)^777
        have hw : |(-1100631753/5000000000 : ℝ)|=(1100631753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078963003/2000000000 : ℝ)|^1033 ≤ (22011024336953/50000000000000 : ℝ)^777
        have hw : |(1078963003/2000000000 : ℝ)|=(1078963003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264028507/10000000000 : ℝ)|^1033 ≤ (10652224481897/25000000000000 : ℝ)^777
        have hw : |(5264028507/10000000000 : ℝ)|=(5264028507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s6_1 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5345102943/10000000000 : ℝ)*x 0 + (-45352537/200000000 : ℝ)*x 1 + (5264028539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345102943/10000000000 : ℝ)^1033 ≤ (2174178176209/5000000000000 : ℝ)^777 := by
    have hnat : (5345102943 : ℕ)^1033*5000000000000^777 ≤ 2174178176209^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345102943 10000000000 2174178176209 5000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45352537/200000000 : ℝ)^1033 ≤ (3476884549519/25000000000000 : ℝ)^777 := by
    have hnat : (45352537 : ℕ)^1033*25000000000000^777 ≤ 3476884549519^777*200000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45352537 200000000 3476884549519 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264028539/10000000000 : ℝ)^1033 ≤ (42608898271947/100000000000000 : ℝ)^777 := by
    have hnat : (5264028539 : ℕ)^1033*100000000000000^777 ≤ 42608898271947^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264028539 10000000000 42608898271947 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345102943/10000000000 : ℝ), (-45352537/200000000 : ℝ), (5264028539/10000000000 : ℝ)] ![(2174178176209/5000000000000 : ℝ), (3476884549519/25000000000000 : ℝ), (42608898271947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345102943/10000000000 : ℝ)|^1033 ≤ (2174178176209/5000000000000 : ℝ)^777
        have hw : |(5345102943/10000000000 : ℝ)|=(5345102943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45352537/200000000 : ℝ)|^1033 ≤ (3476884549519/25000000000000 : ℝ)^777
        have hw : |(-45352537/200000000 : ℝ)|=(45352537/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264028539/10000000000 : ℝ)|^1033 ≤ (42608898271947/100000000000000 : ℝ)^777
        have hw : |(5264028539/10000000000 : ℝ)|=(5264028539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s6_2 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672551401/5000000000 : ℝ)*x 0 + (5264028619/10000000000 : ℝ)*x 1 + (-2267626931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672551401/5000000000 : ℝ)^1033 ≤ (10870890499797/25000000000000 : ℝ)^777 := by
    have hnat : (2672551401 : ℕ)^1033*25000000000000^777 ≤ 10870890499797^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672551401 5000000000 10870890499797 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264028619/10000000000 : ℝ)^1033 ≤ (10652224783211/25000000000000 : ℝ)^777 := by
    have hnat : (5264028619 : ℕ)^1033*25000000000000^777 ≤ 10652224783211^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264028619 10000000000 10652224783211 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2267626931/10000000000 : ℝ)^1033 ≤ (1390753885853/10000000000000 : ℝ)^777 := by
    have hnat : (2267626931 : ℕ)^1033*10000000000000^777 ≤ 1390753885853^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267626931 10000000000 1390753885853 10000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672551401/5000000000 : ℝ), (5264028619/10000000000 : ℝ), (-2267626931/10000000000 : ℝ)] ![(10870890499797/25000000000000 : ℝ), (10652224783211/25000000000000 : ℝ), (1390753885853/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672551401/5000000000 : ℝ)|^1033 ≤ (10870890499797/25000000000000 : ℝ)^777
        have hw : |(2672551401/5000000000 : ℝ)|=(2672551401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264028619/10000000000 : ℝ)|^1033 ≤ (10652224783211/25000000000000 : ℝ)^777
        have hw : |(5264028619/10000000000 : ℝ)|=(5264028619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2267626931/10000000000 : ℝ)|^1033 ≤ (1390753885853/10000000000000 : ℝ)^777
        have hw : |(-2267626931/10000000000 : ℝ)|=(2267626931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s6_3 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1093686617/2500000000 : ℝ)*x 0 + (2124180447/5000000000 : ℝ)*x 1 + (4504938743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093686617/2500000000 : ℝ)^1033 ≤ (33316302847707/100000000000000 : ℝ)^777 := by
    have hnat : (1093686617 : ℕ)^1033*100000000000000^777 ≤ 33316302847707^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093686617 2500000000 33316302847707 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124180447/5000000000 : ℝ)^1033 ≤ (8010703373333/25000000000000 : ℝ)^777 := by
    have hnat : (2124180447 : ℕ)^1033*25000000000000^777 ≤ 8010703373333^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124180447 5000000000 8010703373333 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504938743/10000000000 : ℝ)^1033 ≤ (34640883643859/100000000000000 : ℝ)^777 := by
    have hnat : (4504938743 : ℕ)^1033*100000000000000^777 ≤ 34640883643859^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504938743 10000000000 34640883643859 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093686617/2500000000 : ℝ), (2124180447/5000000000 : ℝ), (4504938743/10000000000 : ℝ)] ![(33316302847707/100000000000000 : ℝ), (8010703373333/25000000000000 : ℝ), (34640883643859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093686617/2500000000 : ℝ)|^1033 ≤ (33316302847707/100000000000000 : ℝ)^777
        have hw : |(1093686617/2500000000 : ℝ)|=(1093686617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2124180447/5000000000 : ℝ)|^1033 ≤ (8010703373333/25000000000000 : ℝ)^777
        have hw : |(2124180447/5000000000 : ℝ)|=(2124180447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504938743/10000000000 : ℝ)|^1033 ≤ (34640883643859/100000000000000 : ℝ)^777
        have hw : |(4504938743/10000000000 : ℝ)|=(4504938743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s6_4 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1100634351/5000000000 : ℝ)*x 0 + (5264358849/10000000000 : ℝ)*x 1 + (5394483459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100634351/5000000000 : ℝ)^1033 ≤ (334227383339/2500000000000 : ℝ)^777 := by
    have hnat : (1100634351 : ℕ)^1033*2500000000000^777 ≤ 334227383339^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100634351 5000000000 334227383339 2500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264358849/10000000000 : ℝ)^1033 ≤ (42612452846141/100000000000000 : ℝ)^777 := by
    have hnat : (5264358849 : ℕ)^1033*100000000000000^777 ≤ 42612452846141^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264358849 10000000000 42612452846141 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394483459/10000000000 : ℝ)^1033 ≤ (22009225898857/50000000000000 : ℝ)^777 := by
    have hnat : (5394483459 : ℕ)^1033*50000000000000^777 ≤ 22009225898857^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394483459 10000000000 22009225898857 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1100634351/5000000000 : ℝ), (5264358849/10000000000 : ℝ), (5394483459/10000000000 : ℝ)] ![(334227383339/2500000000000 : ℝ), (42612452846141/100000000000000 : ℝ), (22009225898857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1100634351/5000000000 : ℝ)|^1033 ≤ (334227383339/2500000000000 : ℝ)^777
        have hw : |(-1100634351/5000000000 : ℝ)|=(1100634351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264358849/10000000000 : ℝ)|^1033 ≤ (42612452846141/100000000000000 : ℝ)^777
        have hw : |(5264358849/10000000000 : ℝ)|=(5264358849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394483459/10000000000 : ℝ)|^1033 ≤ (22009225898857/50000000000000 : ℝ)^777
        have hw : |(5394483459/10000000000 : ℝ)|=(5394483459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s6_5 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312147433/10000000000 : ℝ)*x 0 + (-427434393/2000000000 : ℝ)*x 1 + (5394483457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312147433/10000000000 : ℝ)^1033 ≤ (1078187357239/2500000000000 : ℝ)^777 := by
    have hnat : (5312147433 : ℕ)^1033*2500000000000^777 ≤ 1078187357239^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312147433 10000000000 1078187357239 2500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427434393/2000000000 : ℝ)^1033 ≤ (1285405391391/10000000000000 : ℝ)^777 := by
    have hnat : (427434393 : ℕ)^1033*10000000000000^777 ≤ 1285405391391^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427434393 2000000000 1285405391391 10000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394483457/10000000000 : ℝ)^1033 ≤ (44018451776017/100000000000000 : ℝ)^777 := by
    have hnat : (5394483457 : ℕ)^1033*100000000000000^777 ≤ 44018451776017^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394483457 10000000000 44018451776017 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312147433/10000000000 : ℝ), (-427434393/2000000000 : ℝ), (5394483457/10000000000 : ℝ)] ![(1078187357239/2500000000000 : ℝ), (1285405391391/10000000000000 : ℝ), (44018451776017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312147433/10000000000 : ℝ)|^1033 ≤ (1078187357239/2500000000000 : ℝ)^777
        have hw : |(5312147433/10000000000 : ℝ)|=(5312147433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427434393/2000000000 : ℝ)|^1033 ≤ (1285405391391/10000000000000 : ℝ)^777
        have hw : |(-427434393/2000000000 : ℝ)|=(427434393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394483457/10000000000 : ℝ)|^1033 ≤ (44018451776017/100000000000000 : ℝ)^777
        have hw : |(5394483457/10000000000 : ℝ)|=(5394483457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s6_6 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1062429459/2000000000 : ℝ)*x 0 + (5394483647/10000000000 : ℝ)*x 1 + (-1068585947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062429459/2000000000 : ℝ)^1033 ≤ (43127492800053/100000000000000 : ℝ)^777 := by
    have hnat : (1062429459 : ℕ)^1033*100000000000000^777 ≤ 43127492800053^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062429459 2000000000 43127492800053 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394483647/10000000000 : ℝ)^1033 ≤ (22009226918603/50000000000000 : ℝ)^777 := by
    have hnat : (5394483647 : ℕ)^1033*50000000000000^777 ≤ 22009226918603^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394483647 10000000000 22009226918603 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1068585947/5000000000 : ℝ)^1033 ≤ (1606756668273/12500000000000 : ℝ)^777 := by
    have hnat : (1068585947 : ℕ)^1033*12500000000000^777 ≤ 1606756668273^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068585947 5000000000 1606756668273 12500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062429459/2000000000 : ℝ), (5394483647/10000000000 : ℝ), (-1068585947/5000000000 : ℝ)] ![(43127492800053/100000000000000 : ℝ), (22009226918603/50000000000000 : ℝ), (1606756668273/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062429459/2000000000 : ℝ)|^1033 ≤ (43127492800053/100000000000000 : ℝ)^777
        have hw : |(1062429459/2000000000 : ℝ)|=(1062429459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394483647/10000000000 : ℝ)|^1033 ≤ (22009226918603/50000000000000 : ℝ)^777
        have hw : |(5394483647/10000000000 : ℝ)|=(5394483647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1068585947/5000000000 : ℝ)|^1033 ≤ (1606756668273/12500000000000 : ℝ)^777
        have hw : |(-1068585947/5000000000 : ℝ)|=(1068585947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s6_7 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4374756621/10000000000 : ℝ)*x 0 + (2252145339/5000000000 : ℝ)*x 1 + (2124505659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374756621/10000000000 : ℝ)^1033 ≤ (16658202822037/50000000000000 : ℝ)^777 := by
    have hnat : (4374756621 : ℕ)^1033*50000000000000^777 ≤ 16658202822037^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374756621 10000000000 16658202822037 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252145339/5000000000 : ℝ)^1033 ≤ (3463425861691/10000000000000 : ℝ)^777 := by
    have hnat : (2252145339 : ℕ)^1033*10000000000000^777 ≤ 3463425861691^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252145339 5000000000 3463425861691 10000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124505659/5000000000 : ℝ)^1033 ≤ (400616696531/1250000000000 : ℝ)^777 := by
    have hnat : (2124505659 : ℕ)^1033*1250000000000^777 ≤ 400616696531^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124505659 5000000000 400616696531 1250000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374756621/10000000000 : ℝ), (2252145339/5000000000 : ℝ), (2124505659/5000000000 : ℝ)] ![(16658202822037/50000000000000 : ℝ), (3463425861691/10000000000000 : ℝ), (400616696531/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374756621/10000000000 : ℝ)|^1033 ≤ (16658202822037/50000000000000 : ℝ)^777
        have hw : |(4374756621/10000000000 : ℝ)|=(4374756621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252145339/5000000000 : ℝ)|^1033 ≤ (3463425861691/10000000000000 : ℝ)^777
        have hw : |(2252145339/5000000000 : ℝ)|=(2252145339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124505659/5000000000 : ℝ)|^1033 ≤ (400616696531/1250000000000 : ℝ)^777
        have hw : |(2124505659/5000000000 : ℝ)|=(2124505659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1071_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11247/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7009/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (703/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5603/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (703/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5603/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (703/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5603/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (703/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5603/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (703/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5603/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (703/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5603/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5603/50000 : ℝ) ^ (8263/2048 : ℝ) ≤ (14616683941617299/100000000000000000000 : ℝ) := by
    have hpowers : (5603/50000 : ℝ)^8263 ≤ (14616683941617299/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5603 : ℕ)^8263*100000000000000000000^2048 ≤ 14616683941617299^2048*50000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5603 50000 14616683941617299 100000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5603/50000 : ℝ)) (X := (14616683941617299/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (703/5000 : ℝ) ^ (8263/2048 : ℝ) ≤ (36509313302757843/100000000000000000000 : ℝ) := by
    have hpowers : (703/5000 : ℝ)^8263 ≤ (36509313302757843/100000000000000000000 : ℝ)^2048 := by
      have hnat : (703 : ℕ)^8263*100000000000000000000^2048 ≤ 36509313302757843^2048*5000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        703 5000 36509313302757843 100000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (703/5000 : ℝ)) (X := (36509313302757843/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014616683941617299/50000000000000000000 : ℝ) ≤ (1250090559355713/1250000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (50014616683941617299/50000000000000000000 : ℝ)^2048 ≤ (1250090559355713/1250000000000000 : ℝ)^8263 := by
      have hnat : (50014616683941617299 : ℕ)^2048*1250000000000000^8263 ≤ 1250090559355713^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014616683941617299 50000000000000000000 1250090559355713 1250000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250090559355713/1250000000000000 : ℝ)) (X := (50014616683941617299/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025562998622187571/50000000000000000000 : ℝ) ≤ (2000253384766709/2000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (50025562998622187571/50000000000000000000 : ℝ)^2048 ≤ (2000253384766709/2000000000000000 : ℝ)^8263 := by
      have hnat : (50025562998622187571 : ℕ)^2048*2000000000000000^8263 ≤ 2000253384766709^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025562998622187571 50000000000000000000 2000253384766709 2000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000253384766709/2000000000000000 : ℝ)) (X := (50025562998622187571/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036509313302757843/50000000000000000000 : ℝ) ≤ (5000904686410693/5000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (50036509313302757843/50000000000000000000 : ℝ)^2048 ≤ (5000904686410693/5000000000000000 : ℝ)^8263 := by
      have hnat : (50036509313302757843 : ℕ)^2048*5000000000000000^8263 ≤ 5000904686410693^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036509313302757843 50000000000000000000 5000904686410693 5000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000904686410693/5000000000000000 : ℝ)) (X := (50036509313302757843/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14616683941617299/100000000000000000000 : ℝ) ≤ ((7132477571123536681/7135000000000000000 : ℝ)+2*(542448987841/285400000000000 : ℝ)*(5603/50000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (7132477571123536681/7135000000000000000 : ℝ)+2*(542448987841/285400000000000 : ℝ)*(5603/50000 : ℝ)=(1250090559355713/1250000000000000 : ℝ) by norm_num, show 1+2*(14616683941617299/100000000000000000000 : ℝ)=(50014616683941617299/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36509313302757843/100000000000000000000 : ℝ)+(14616683941617299/100000000000000000000 : ℝ) ≤ ((7132477571123536681/7135000000000000000 : ℝ)+(542448987841/285400000000000 : ℝ)*((703/5000 : ℝ)+(5603/50000 : ℝ)))^(8263/2048 : ℝ) := by
    rw [show (7132477571123536681/7135000000000000000 : ℝ)+(542448987841/285400000000000 : ℝ)*((703/5000 : ℝ)+(5603/50000 : ℝ))=(2000253384766709/2000000000000000 : ℝ) by norm_num, show 1+(36509313302757843/100000000000000000000 : ℝ)+(14616683941617299/100000000000000000000 : ℝ)=(50025562998622187571/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36509313302757843/100000000000000000000 : ℝ) ≤ ((7132477571123536681/7135000000000000000 : ℝ)+2*(542448987841/285400000000000 : ℝ)*(703/5000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (7132477571123536681/7135000000000000000 : ℝ)+2*(542448987841/285400000000000 : ℝ)*(703/5000 : ℝ)=(5000904686410693/5000000000000000 : ℝ) by norm_num, show 1+2*(36509313302757843/100000000000000000000 : ℝ)=(50036509313302757843/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7132477571123536681/7135000000000000000 : ℝ)*(X 1 0+X 2 0)+(542448987841/285400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (5603/50000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (7132477571123536681/7135000000000000000 : ℝ)) (alpha := (542448987841/285400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7132477571123536681/7135000000000000000 : ℝ)*(X 0 1+X 2 1)+(542448987841/285400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (5603/50000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (7132477571123536681/7135000000000000000 : ℝ)) (alpha := (542448987841/285400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7132477571123536681/7135000000000000000 : ℝ)*(X 0 2+X 1 2)+(542448987841/285400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (5603/50000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (7132477571123536681/7135000000000000000 : ℝ)) (alpha := (542448987841/285400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1100631753/5000000000 : ℝ)*X 0 0+(1078963003/2000000000 : ℝ)*X 0 1+(5264028507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345102943/10000000000 : ℝ)*X 1 0+(-45352537/200000000 : ℝ)*X 1 1+(5264028539/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672551401/5000000000 : ℝ)*X 2 0+(5264028619/10000000000 : ℝ)*X 2 1+(-2267626931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093686617/2500000000 : ℝ)*X 0 0+(2124180447/5000000000 : ℝ)*X 0 1+(4504938743/10000000000 : ℝ)*X 0 2+(1093686617/2500000000 : ℝ)*X 1 0+(2124180447/5000000000 : ℝ)*X 1 1+(4504938743/10000000000 : ℝ)*X 1 2+(1093686617/2500000000 : ℝ)*X 2 0+(2124180447/5000000000 : ℝ)*X 2 1+(4504938743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1100634351/5000000000 : ℝ)*X 0 0+(5264358849/10000000000 : ℝ)*X 0 1+(5394483459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312147433/10000000000 : ℝ)*X 1 0+(-427434393/2000000000 : ℝ)*X 1 1+(5394483457/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062429459/2000000000 : ℝ)*X 2 0+(5394483647/10000000000 : ℝ)*X 2 1+(-1068585947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4374756621/10000000000 : ℝ)*X 0 0+(2252145339/5000000000 : ℝ)*X 0 1+(2124505659/5000000000 : ℝ)*X 0 2+(4374756621/10000000000 : ℝ)*X 1 0+(2252145339/5000000000 : ℝ)*X 1 1+(2124505659/5000000000 : ℝ)*X 1 2+(4374756621/10000000000 : ℝ)*X 2 0+(2252145339/5000000000 : ℝ)*X 2 1+(2124505659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1674721906399458414017366841/178375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1995435051/100000000000000 : ℝ)*(base19) + (430500473/25000000000000 : ℝ)*(base23) + (38342013/100000000000000 : ℝ)*(lower2) + (319356089/100000000000000 : ℝ)*(upper3) + (100634177/100000000000000 : ℝ)*(upper5) + (5771834978479287/100000000000000 : ℝ)*(major0) + (5771834978479287/100000000000000 : ℝ)*(major1) + (5771834978479287/100000000000000 : ℝ)*(major2) + (7646109711229789/100000000000000 : ℝ)*(sp0) + (238942423514347/3125000000000 : ℝ)*(sp1) + (7646157825892263/100000000000000 : ℝ)*(sp2) + (389747941420779/10000000000000 : ℝ)*(sp3) + (24918332183/50000000000000 : ℝ)*(sp4) + (30681897609/100000000000000 : ℝ)*(sp7) + (1948755048052699/50000000000000 : ℝ)*(f.failure) + (1529231909578831/20000000000000 : ℝ)*(f.sum) + (61784422023243/14270000000000000000000000000 : ℝ)*base66 + (12832636144791098553/713500000000000000000000000000000 : ℝ)*base68 + (1488626034715901447/713500000000000000000000000000000 : ℝ)*base69 + (3541609136166098553/713500000000000000000000000000000 : ℝ)*base72 + (126867880224373/14270000000000000000000000000 : ℝ)*base74 + (6817264595110598553/713500000000000000000000000000000 : ℝ)*base76 + (3137680984995098553/713500000000000000000000000000000 : ℝ)*base78 + (14284693000469098553/713500000000000000000000000000000 : ℝ)*base80 + (22128948736963/14270000000000000000000000000 : ℝ)*base82 + (3697963/1000000000000000000000 : ℝ)*base90 + (3697963/1000000000000000000000 : ℝ)*base92 + (3697963/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (929385306446325936207349101/89187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (131706427/6250000000000 : ℝ)*(base19) + (999661377/50000000000000 : ℝ)*(base23) + (125717217/50000000000000 : ℝ)*(upper3) + (2987011/10000000000000 : ℝ)*(lower4) + (27852783/12500000000000 : ℝ)*(upper5) + (1450276803259107/25000000000000 : ℝ)*(major0) + (1450276803259107/25000000000000 : ℝ)*(major1) + (1450276803259107/25000000000000 : ℝ)*(major2) + (11000740991/20000000000000 : ℝ)*(sp1) + (60714861689/100000000000000 : ℝ)*(sp2) + (7684937507975947/100000000000000 : ℝ)*(sp4) + (48030502481051/625000000000 : ℝ)*(sp5) + (1536974958758301/20000000000000 : ℝ)*(sp6) + (3917276570744297/100000000000000 : ℝ)*(sp7) + (3917276570744297/100000000000000 : ℝ)*(f.failure) + (7684937507975947/100000000000000 : ℝ)*(f.sum) + (1221718466831/7135000000000000000000000000 : ℝ)*base66 + (212740427808896133/178375000000000000000000000000000 : ℝ)*base68 + (108738125965146133/178375000000000000000000000000000 : ℝ)*base70 + (458611715709728867/178375000000000000000000000000000 : ℝ)*base71 + (14321776874907/3567500000000000000000000000 : ℝ)*base73 + (3546038501838146133/178375000000000000000000000000000 : ℝ)*base76 + (459474032545228867/178375000000000000000000000000000 : ℝ)*base77 + (3013957699711521133/178375000000000000000000000000000 : ℝ)*base80 + (21327615137179/7135000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (14563289/2000000000000000000000 : ℝ)*base90 + (14563289/2000000000000000000000 : ℝ)*base92 + (14563289/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1071_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1071_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1071_s7_0 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1100649899/5000000000 : ℝ)*x 0 + (2697183819/5000000000 : ℝ)*x 1 + (2632226137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100649899/5000000000 : ℝ)^1033 ≤ (13369346414533/100000000000000 : ℝ)^777 := by
    have hnat : (1100649899 : ℕ)^1033*100000000000000^777 ≤ 13369346414533^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100649899 5000000000 13369346414533 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697183819/5000000000 : ℝ)^1033 ≤ (44017195333931/100000000000000 : ℝ)^777 := by
    have hnat : (2697183819 : ℕ)^1033*100000000000000^777 ≤ 44017195333931^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697183819 5000000000 44017195333931 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632226137/5000000000 : ℝ)^1033 ≤ (1704538329461/4000000000000 : ℝ)^777 := by
    have hnat : (2632226137 : ℕ)^1033*4000000000000^777 ≤ 1704538329461^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632226137 5000000000 1704538329461 4000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1100649899/5000000000 : ℝ), (2697183819/5000000000 : ℝ), (2632226137/5000000000 : ℝ)] ![(13369346414533/100000000000000 : ℝ), (44017195333931/100000000000000 : ℝ), (1704538329461/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1100649899/5000000000 : ℝ)|^1033 ≤ (13369346414533/100000000000000 : ℝ)^777
        have hw : |(-1100649899/5000000000 : ℝ)|=(1100649899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697183819/5000000000 : ℝ)|^1033 ≤ (44017195333931/100000000000000 : ℝ)^777
        have hw : |(2697183819/5000000000 : ℝ)|=(2697183819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632226137/5000000000 : ℝ)|^1033 ≤ (1704538329461/4000000000000 : ℝ)^777
        have hw : |(2632226137/5000000000 : ℝ)|=(2632226137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s7_1 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344992017/10000000000 : ℝ)*x 0 + (-1133607107/5000000000 : ℝ)*x 1 + (5264452663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344992017/10000000000 : ℝ)^1033 ≤ (43482363803281/100000000000000 : ℝ)^777 := by
    have hnat : (5344992017 : ℕ)^1033*100000000000000^777 ≤ 43482363803281^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344992017 10000000000 43482363803281 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133607107/5000000000 : ℝ)^1033 ≤ (3476043440911/25000000000000 : ℝ)^777 := by
    have hnat : (1133607107 : ℕ)^1033*25000000000000^777 ≤ 3476043440911^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133607107 5000000000 3476043440911 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264452663/10000000000 : ℝ)^1033 ≤ (42613462422749/100000000000000 : ℝ)^777 := by
    have hnat : (5264452663 : ℕ)^1033*100000000000000^777 ≤ 42613462422749^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264452663 10000000000 42613462422749 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344992017/10000000000 : ℝ), (-1133607107/5000000000 : ℝ), (5264452663/10000000000 : ℝ)] ![(43482363803281/100000000000000 : ℝ), (3476043440911/25000000000000 : ℝ), (42613462422749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344992017/10000000000 : ℝ)|^1033 ≤ (43482363803281/100000000000000 : ℝ)^777
        have hw : |(5344992017/10000000000 : ℝ)|=(5344992017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1133607107/5000000000 : ℝ)|^1033 ≤ (3476043440911/25000000000000 : ℝ)^777
        have hw : |(-1133607107/5000000000 : ℝ)|=(1133607107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264452663/10000000000 : ℝ)|^1033 ≤ (42613462422749/100000000000000 : ℝ)^777
        have hw : |(5264452663/10000000000 : ℝ)|=(5264452663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s7_2 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344992147/10000000000 : ℝ)*x 0 + (5264452351/10000000000 : ℝ)*x 1 + (-2267214453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344992147/10000000000 : ℝ)^1033 ≤ (10870591302323/25000000000000 : ℝ)^777 := by
    have hnat : (5344992147 : ℕ)^1033*25000000000000^777 ≤ 10870591302323^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344992147 10000000000 10870591302323 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264452351/10000000000 : ℝ)^1033 ≤ (1065336476629/2500000000000 : ℝ)^777 := by
    have hnat : (5264452351 : ℕ)^1033*2500000000000^777 ≤ 1065336476629^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264452351 10000000000 1065336476629 2500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2267214453/10000000000 : ℝ)^1033 ≤ (3476043928069/25000000000000 : ℝ)^777 := by
    have hnat : (2267214453 : ℕ)^1033*25000000000000^777 ≤ 3476043928069^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267214453 10000000000 3476043928069 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344992147/10000000000 : ℝ), (5264452351/10000000000 : ℝ), (-2267214453/10000000000 : ℝ)] ![(10870591302323/25000000000000 : ℝ), (1065336476629/2500000000000 : ℝ), (3476043928069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344992147/10000000000 : ℝ)|^1033 ≤ (10870591302323/25000000000000 : ℝ)^777
        have hw : |(5344992147/10000000000 : ℝ)|=(5344992147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264452351/10000000000 : ℝ)|^1033 ≤ (1065336476629/2500000000000 : ℝ)^777
        have hw : |(5264452351/10000000000 : ℝ)|=(5264452351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2267214453/10000000000 : ℝ)|^1033 ≤ (3476043928069/25000000000000 : ℝ)^777
        have hw : |(-2267214453/10000000000 : ℝ)|=(2267214453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s7_3 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4374768687/10000000000 : ℝ)*x 0 + (531151643/1250000000 : ℝ)*x 1 + (4504080741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374768687/10000000000 : ℝ)^1033 ≤ (33316527809149/100000000000000 : ℝ)^777 := by
    have hnat : (4374768687 : ℕ)^1033*100000000000000^777 ≤ 33316527809149^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374768687 10000000000 33316527809149 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531151643/1250000000 : ℝ)^1033 ≤ (8012839907843/25000000000000 : ℝ)^777 := by
    have hnat : (531151643 : ℕ)^1033*25000000000000^777 ≤ 8012839907843^777*1250000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531151643 1250000000 8012839907843 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504080741/10000000000 : ℝ)^1033 ≤ (6926422508831/20000000000000 : ℝ)^777 := by
    have hnat : (4504080741 : ℕ)^1033*20000000000000^777 ≤ 6926422508831^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504080741 10000000000 6926422508831 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374768687/10000000000 : ℝ), (531151643/1250000000 : ℝ), (4504080741/10000000000 : ℝ)] ![(33316527809149/100000000000000 : ℝ), (8012839907843/25000000000000 : ℝ), (6926422508831/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374768687/10000000000 : ℝ)|^1033 ≤ (33316527809149/100000000000000 : ℝ)^777
        have hw : |(4374768687/10000000000 : ℝ)|=(4374768687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(531151643/1250000000 : ℝ)|^1033 ≤ (8012839907843/25000000000000 : ℝ)^777
        have hw : |(531151643/1250000000 : ℝ)|=(531151643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504080741/10000000000 : ℝ)|^1033 ≤ (6926422508831/20000000000000 : ℝ)^777
        have hw : |(4504080741/10000000000 : ℝ)|=(4504080741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s7_4 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2201305219/10000000000 : ℝ)*x 0 + (2632389233/5000000000 : ℝ)*x 1 + (2697020007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201305219/10000000000 : ℝ)^1033 ≤ (106955121487/800000000000 : ℝ)^777 := by
    have hnat : (2201305219 : ℕ)^1033*800000000000^777 ≤ 106955121487^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201305219 10000000000 106955121487 800000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632389233/5000000000 : ℝ)^1033 ≤ (4261696858821/10000000000000 : ℝ)^777 := by
    have hnat : (2632389233 : ℕ)^1033*10000000000000^777 ≤ 4261696858821^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632389233 5000000000 4261696858821 10000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697020007/5000000000 : ℝ)^1033 ≤ (44013641210621/100000000000000 : ℝ)^777 := by
    have hnat : (2697020007 : ℕ)^1033*100000000000000^777 ≤ 44013641210621^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697020007 5000000000 44013641210621 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2201305219/10000000000 : ℝ), (2632389233/5000000000 : ℝ), (2697020007/5000000000 : ℝ)] ![(106955121487/800000000000 : ℝ), (4261696858821/10000000000000 : ℝ), (44013641210621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2201305219/10000000000 : ℝ)|^1033 ≤ (106955121487/800000000000 : ℝ)^777
        have hw : |(-2201305219/10000000000 : ℝ)|=(2201305219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632389233/5000000000 : ℝ)|^1033 ≤ (4261696858821/10000000000000 : ℝ)^777
        have hw : |(2632389233/5000000000 : ℝ)|=(2632389233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697020007/5000000000 : ℝ)|^1033 ≤ (44013641210621/100000000000000 : ℝ)^777
        have hw : |(2697020007/5000000000 : ℝ)|=(2697020007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s7_5 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312256683/10000000000 : ℝ)*x 0 + (-1068813347/5000000000 : ℝ)*x 1 + (5394039569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312256683/10000000000 : ℝ)^1033 ≤ (10782168371613/25000000000000 : ℝ)^777 := by
    have hnat : (5312256683 : ℕ)^1033*25000000000000^777 ≤ 10782168371613^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312256683 10000000000 10782168371613 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1068813347/5000000000 : ℝ)^1033 ≤ (12857690114431/100000000000000 : ℝ)^777 := by
    have hnat : (1068813347 : ℕ)^1033*100000000000000^777 ≤ 12857690114431^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068813347 5000000000 12857690114431 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394039569/10000000000 : ℝ)^1033 ≤ (4401363638323/10000000000000 : ℝ)^777 := by
    have hnat : (5394039569 : ℕ)^1033*10000000000000^777 ≤ 4401363638323^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394039569 10000000000 4401363638323 10000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312256683/10000000000 : ℝ), (-1068813347/5000000000 : ℝ), (5394039569/10000000000 : ℝ)] ![(10782168371613/25000000000000 : ℝ), (12857690114431/100000000000000 : ℝ), (4401363638323/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312256683/10000000000 : ℝ)|^1033 ≤ (10782168371613/25000000000000 : ℝ)^777
        have hw : |(5312256683/10000000000 : ℝ)|=(5312256683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1068813347/5000000000 : ℝ)|^1033 ≤ (12857690114431/100000000000000 : ℝ)^777
        have hw : |(-1068813347/5000000000 : ℝ)|=(1068813347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394039569/10000000000 : ℝ)|^1033 ≤ (4401363638323/10000000000000 : ℝ)^777
        have hw : |(5394039569/10000000000 : ℝ)|=(5394039569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s7_6 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (664032051/1250000000 : ℝ)*x 0 + (107880801/200000000 : ℝ)*x 1 + (-2137626413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664032051/1250000000 : ℝ)^1033 ≤ (10782167629553/25000000000000 : ℝ)^777 := by
    have hnat : (664032051 : ℕ)^1033*25000000000000^777 ≤ 10782167629553^777*1250000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664032051 1250000000 10782167629553 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107880801/200000000 : ℝ)^1033 ≤ (343856575009/781250000000 : ℝ)^777 := by
    have hnat : (107880801 : ℕ)^1033*781250000000^777 ≤ 343856575009^777*200000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107880801 200000000 343856575009 781250000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2137626413/10000000000 : ℝ)^1033 ≤ (80360549171/625000000000 : ℝ)^777 := by
    have hnat : (2137626413 : ℕ)^1033*625000000000^777 ≤ 80360549171^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137626413 10000000000 80360549171 625000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664032051/1250000000 : ℝ), (107880801/200000000 : ℝ), (-2137626413/10000000000 : ℝ)] ![(10782167629553/25000000000000 : ℝ), (343856575009/781250000000 : ℝ), (80360549171/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664032051/1250000000 : ℝ)|^1033 ≤ (10782167629553/25000000000000 : ℝ)^777
        have hw : |(664032051/1250000000 : ℝ)|=(664032051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107880801/200000000 : ℝ)|^1033 ≤ (343856575009/781250000000 : ℝ)^777
        have hw : |(107880801/200000000 : ℝ)|=(107880801/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2137626413/10000000000 : ℝ)|^1033 ≤ (80360549171/625000000000 : ℝ)^777
        have hw : |(-2137626413/10000000000 : ℝ)|=(2137626413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s7_7 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (34177951/78125000 : ℝ)*x 0 + (180137699/400000000 : ℝ)*x 1 + (2124927309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34177951/78125000 : ℝ)^1033 ≤ (33316619346967/100000000000000 : ℝ)^777 := by
    have hnat : (34177951 : ℕ)^1033*100000000000000^777 ≤ 33316619346967^777*78125000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34177951 78125000 33316619346967 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180137699/400000000 : ℝ)^1033 ≤ (34625588097399/100000000000000 : ℝ)^777 := by
    have hnat : (180137699 : ℕ)^1033*100000000000000^777 ≤ 34625588097399^777*400000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180137699 400000000 34625588097399 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124927309/5000000000 : ℝ)^1033 ≤ (32057792535843/100000000000000 : ℝ)^777 := by
    have hnat : (2124927309 : ℕ)^1033*100000000000000^777 ≤ 32057792535843^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124927309 5000000000 32057792535843 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34177951/78125000 : ℝ), (180137699/400000000 : ℝ), (2124927309/5000000000 : ℝ)] ![(33316619346967/100000000000000 : ℝ), (34625588097399/100000000000000 : ℝ), (32057792535843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34177951/78125000 : ℝ)|^1033 ≤ (33316619346967/100000000000000 : ℝ)^777
        have hw : |(34177951/78125000 : ℝ)|=(34177951/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180137699/400000000 : ℝ)|^1033 ≤ (34625588097399/100000000000000 : ℝ)^777
        have hw : |(180137699/400000000 : ℝ)|=(180137699/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124927309/5000000000 : ℝ)|^1033 ≤ (32057792535843/100000000000000 : ℝ)^777
        have hw : |(2124927309/5000000000 : ℝ)|=(2124927309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s7_8 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-37091861/10000000000 : ℝ)*x 0 + (1428121377/2500000000 : ℝ)*x 1 + (615370163/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37091861/10000000000 : ℝ)^1033 ≤ (14667739833/25000000000000 : ℝ)^777 := by
    have hnat : (37091861 : ℕ)^1033*25000000000000^777 ≤ 14667739833^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37091861 10000000000 14667739833 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1428121377/2500000000 : ℝ)^1033 ≤ (23750661968901/50000000000000 : ℝ)^777 := by
    have hnat : (1428121377 : ℕ)^1033*50000000000000^777 ≤ 23750661968901^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428121377 2500000000 23750661968901 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (615370163/1000000000 : ℝ)^1033 ≤ (1311000127269/2500000000000 : ℝ)^777 := by
    have hnat : (615370163 : ℕ)^1033*2500000000000^777 ≤ 1311000127269^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615370163 1000000000 1311000127269 2500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37091861/10000000000 : ℝ), (1428121377/2500000000 : ℝ), (615370163/1000000000 : ℝ)] ![(14667739833/25000000000000 : ℝ), (23750661968901/50000000000000 : ℝ), (1311000127269/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37091861/10000000000 : ℝ)|^1033 ≤ (14667739833/25000000000000 : ℝ)^777
        have hw : |(-37091861/10000000000 : ℝ)|=(37091861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1428121377/2500000000 : ℝ)|^1033 ≤ (23750661968901/50000000000000 : ℝ)^777
        have hw : |(1428121377/2500000000 : ℝ)|=(1428121377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(615370163/1000000000 : ℝ)|^1033 ≤ (1311000127269/2500000000000 : ℝ)^777
        have hw : |(615370163/1000000000 : ℝ)|=(615370163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s7_9 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1380890603/10000000000 : ℝ)*x 0 + (5612628173/10000000000 : ℝ)*x 1 + (561322483/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380890603/10000000000 : ℝ)^1033 ≤ (1438452558439/20000000000000 : ℝ)^777 := by
    have hnat : (1380890603 : ℕ)^1033*20000000000000^777 ≤ 1438452558439^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380890603 10000000000 1438452558439 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5612628173/10000000000 : ℝ)^1033 ≤ (11600147403941/25000000000000 : ℝ)^777 := by
    have hnat : (5612628173 : ℕ)^1033*25000000000000^777 ≤ 11600147403941^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5612628173 10000000000 11600147403941 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561322483/1000000000 : ℝ)^1033 ≤ (2900446723591/6250000000000 : ℝ)^777 := by
    have hnat : (561322483 : ℕ)^1033*6250000000000^777 ≤ 2900446723591^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561322483 1000000000 2900446723591 6250000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1380890603/10000000000 : ℝ), (5612628173/10000000000 : ℝ), (561322483/1000000000 : ℝ)] ![(1438452558439/20000000000000 : ℝ), (11600147403941/25000000000000 : ℝ), (2900446723591/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1380890603/10000000000 : ℝ)|^1033 ≤ (1438452558439/20000000000000 : ℝ)^777
        have hw : |(1380890603/10000000000 : ℝ)|=(1380890603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5612628173/10000000000 : ℝ)|^1033 ≤ (11600147403941/25000000000000 : ℝ)^777
        have hw : |(5612628173/10000000000 : ℝ)|=(5612628173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561322483/1000000000 : ℝ)|^1033 ≤ (2900446723591/6250000000000 : ℝ)^777
        have hw : |(561322483/1000000000 : ℝ)|=(561322483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1071_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1407/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1751/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7009/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11247/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7009/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11247/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7009/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11247/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7009/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11247/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7009/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11247/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7009/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11247/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11247/100000 : ℝ) ^ (8263/2048 : ℝ) ≤ (14833654192603299/100000000000000000000 : ℝ) := by
    have hpowers : (11247/100000 : ℝ)^8263 ≤ (14833654192603299/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11247 : ℕ)^8263*100000000000000000000^2048 ≤ 14833654192603299^2048*100000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11247 100000 14833654192603299 100000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11247/100000 : ℝ)) (X := (14833654192603299/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7009/50000 : ℝ) ^ (8263/2048 : ℝ) ≤ (225445504035481/625000000000000000 : ℝ) := by
    have hpowers : (7009/50000 : ℝ)^8263 ≤ (225445504035481/625000000000000000 : ℝ)^2048 := by
      have hnat : (7009 : ℕ)^8263*625000000000000000^2048 ≤ 225445504035481^2048*50000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7009 50000 225445504035481 625000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7009/50000 : ℝ)) (X := (225445504035481/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014833654192603299/50000000000000000000 : ℝ) ≤ (1000073522776039/1000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (50014833654192603299/50000000000000000000 : ℝ)^2048 ≤ (1000073522776039/1000000000000000 : ℝ)^8263 := by
      have hnat : (50014833654192603299 : ℕ)^2048*1000000000000000^8263 ≤ 1000073522776039^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014833654192603299 50000000000000000000 1000073522776039 1000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000073522776039/1000000000000000 : ℝ)) (X := (50014833654192603299/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050904934838280259/100000000000000000000 : ℝ) ≤ (10001261446861923/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (100050904934838280259/100000000000000000000 : ℝ)^2048 ≤ (10001261446861923/10000000000000000 : ℝ)^8263 := by
      have hnat : (100050904934838280259 : ℕ)^2048*10000000000000000^8263 ≤ 10001261446861923^8263*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050904934838280259 100000000000000000000 10001261446861923 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001261446861923/10000000000000000 : ℝ)) (X := (100050904934838280259/100000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (312725445504035481/312500000000000000 : ℝ) ≤ (156277932280679/156250000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (312725445504035481/312500000000000000 : ℝ)^2048 ≤ (156277932280679/156250000000000 : ℝ)^8263 := by
      have hnat : (312725445504035481 : ℕ)^2048*156250000000000^8263 ≤ 156277932280679^8263*312500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312725445504035481 312500000000000000 156277932280679 156250000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156277932280679/156250000000000 : ℝ)) (X := (312725445504035481/312500000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14833654192603299/100000000000000000000 : ℝ) ≤ ((42484970158978769/42500000000000000 : ℝ)+2*(526219101533/277100000000000 : ℝ)*(11247/100000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (42484970158978769/42500000000000000 : ℝ)+2*(526219101533/277100000000000 : ℝ)*(11247/100000 : ℝ)=(1000073522776039/1000000000000000 : ℝ) by norm_num, show 1+2*(14833654192603299/100000000000000000000 : ℝ)=(50014833654192603299/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(225445504035481/625000000000000000 : ℝ)+(14833654192603299/100000000000000000000 : ℝ) ≤ ((42484970158978769/42500000000000000 : ℝ)+(526219101533/277100000000000 : ℝ)*((7009/50000 : ℝ)+(11247/100000 : ℝ)))^(8263/2048 : ℝ) := by
    rw [show (42484970158978769/42500000000000000 : ℝ)+(526219101533/277100000000000 : ℝ)*((7009/50000 : ℝ)+(11247/100000 : ℝ))=(10001261446861923/10000000000000000 : ℝ) by norm_num, show 1+(225445504035481/625000000000000000 : ℝ)+(14833654192603299/100000000000000000000 : ℝ)=(100050904934838280259/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(225445504035481/625000000000000000 : ℝ) ≤ ((42484970158978769/42500000000000000 : ℝ)+2*(526219101533/277100000000000 : ℝ)*(7009/50000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (42484970158978769/42500000000000000 : ℝ)+2*(526219101533/277100000000000 : ℝ)*(7009/50000 : ℝ)=(156277932280679/156250000000000 : ℝ) by norm_num, show 1+2*(225445504035481/625000000000000000 : ℝ)=(312725445504035481/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (42484970158978769/42500000000000000 : ℝ)*(X 1 0+X 2 0)+(526219101533/277100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (7009/50000 : ℝ)) (c := (42484970158978769/42500000000000000 : ℝ)) (alpha := (526219101533/277100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (42484970158978769/42500000000000000 : ℝ)*(X 0 1+X 2 1)+(526219101533/277100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (7009/50000 : ℝ)) (c := (42484970158978769/42500000000000000 : ℝ)) (alpha := (526219101533/277100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (42484970158978769/42500000000000000 : ℝ)*(X 0 2+X 1 2)+(526219101533/277100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (7009/50000 : ℝ)) (c := (42484970158978769/42500000000000000 : ℝ)) (alpha := (526219101533/277100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1100649899/5000000000 : ℝ)*X 0 0+(2697183819/5000000000 : ℝ)*X 0 1+(2632226137/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344992017/10000000000 : ℝ)*X 1 0+(-1133607107/5000000000 : ℝ)*X 1 1+(5264452663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344992147/10000000000 : ℝ)*X 2 0+(5264452351/10000000000 : ℝ)*X 2 1+(-2267214453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374768687/10000000000 : ℝ)*X 0 0+(531151643/1250000000 : ℝ)*X 0 1+(4504080741/10000000000 : ℝ)*X 0 2+(4374768687/10000000000 : ℝ)*X 1 0+(531151643/1250000000 : ℝ)*X 1 1+(4504080741/10000000000 : ℝ)*X 1 2+(4374768687/10000000000 : ℝ)*X 2 0+(531151643/1250000000 : ℝ)*X 2 1+(4504080741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2201305219/10000000000 : ℝ)*X 0 0+(2632389233/5000000000 : ℝ)*X 0 1+(2697020007/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312256683/10000000000 : ℝ)*X 1 0+(-1068813347/5000000000 : ℝ)*X 1 1+(5394039569/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664032051/1250000000 : ℝ)*X 2 0+(107880801/200000000 : ℝ)*X 2 1+(-2137626413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((34177951/78125000 : ℝ)*X 0 0+(180137699/400000000 : ℝ)*X 0 1+(2124927309/5000000000 : ℝ)*X 0 2+(34177951/78125000 : ℝ)*X 1 0+(180137699/400000000 : ℝ)*X 1 1+(2124927309/5000000000 : ℝ)*X 1 2+(34177951/78125000 : ℝ)*X 2 0+(180137699/400000000 : ℝ)*X 2 1+(2124927309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-37091861/10000000000 : ℝ)*X 0 0+(1428121377/2500000000 : ℝ)*X 0 1+(615370163/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1380890603/10000000000 : ℝ)*X 0 0+(5612628173/10000000000 : ℝ)*X 0 1+(561322483/1000000000 : ℝ)*X 0 2+(1380890603/10000000000 : ℝ)*X 1 0+(5612628173/10000000000 : ℝ)*X 1 1+(561322483/1000000000 : ℝ)*X 1 2+(1380890603/10000000000 : ℝ)*X 2 0+(5612628173/10000000000 : ℝ)*X 2 1+(561322483/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s7_9 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (976099586477664506039953047/69275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (843617687/100000000000000 : ℝ)*(lower2) + (318438159/100000000000000 : ℝ)*(lower3) + (795708871/100000000000000 : ℝ)*(lower4) + (162487231/50000000000000 : ℝ)*(lower5) + (1162095721402367/20000000000000 : ℝ)*(major0) + (1162095721402367/20000000000000 : ℝ)*(major1) + (1162095721402367/20000000000000 : ℝ)*(major2) + (7697344028073969/100000000000000 : ℝ)*(sp0) + (192433622562953/2500000000000 : ℝ)*(sp1) + (7697328969943077/100000000000000 : ℝ)*(sp2) + (3923604732025747/100000000000000 : ℝ)*(sp3) + (888725747/12500000000000 : ℝ)*(sp5) + (23042381019/100000000000000 : ℝ)*(sp6) + (499015633/6250000000000 : ℝ)*(sp8) + (3923604732025747/100000000000000 : ℝ)*(f.failure) + (30067781298141/390625000000 : ℝ)*(f.sum) + (57657404585369/1385500000000000000000000000 : ℝ)*base66 + (243678419190990651/138550000000000000000000000000000 : ℝ)*base68 + (2787667549855440651/138550000000000000000000000000000 : ℝ)*base70 + (8442770494572359349/138550000000000000000000000000000 : ℝ)*base71 + (474371405813/2771000000000000000000000000 : ℝ)*base74 + (1645025438026340651/138550000000000000000000000000000 : ℝ)*base76 + (5956059096534290651/138550000000000000000000000000000 : ℝ)*base78 + (642532446828959349/138550000000000000000000000000000 : ℝ)*base79 + (858808176791/1385500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (7731939/2000000000000000000000 : ℝ)*base90 + (7731939/2000000000000000000000 : ℝ)*base92 + (7731939/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (916473255150241507532968251/173187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20737967/25000000000000 : ℝ)*(lower2) + (20949887/2500000000000 : ℝ)*(lower3) + (59139791/20000000000000 : ℝ)*(lower4) + (50187309/25000000000000 : ℝ)*(lower5) + (2919923440929689/50000000000000 : ℝ)*(major0) + (2919923440929689/50000000000000 : ℝ)*(major1) + (2919923440929689/50000000000000 : ℝ)*(major2) + (2259756667/10000000000000 : ℝ)*(sp3) + (193406275719509/2500000000000 : ℝ)*(sp4) + (7736257528148093/100000000000000 : ℝ)*(sp5) + (7736257528148093/100000000000000 : ℝ)*(sp6) + (3943412642594007/100000000000000 : ℝ)*(sp7) + (6499367733/100000000000000 : ℝ)*(sp8) + (819016709/100000000000000 : ℝ)*(sp9) + (1971718029588693/50000000000000 : ℝ)*(f.failure) + (7736257528148093/100000000000000 : ℝ)*(f.sum) + (18572048180337/6927500000000000000000000000 : ℝ)*base65 + (610314272857851917/346375000000000000000000000000000 : ℝ)*base68 + (1904212528115898083/346375000000000000000000000000000 : ℝ)*base69 + (20060154943233898083/346375000000000000000000000000000 : ℝ)*base71 + (7530092647563/6927500000000000000000000000 : ℝ)*base74 + (191366647731273083/346375000000000000000000000000000 : ℝ)*base75 + (2824786264274523083/346375000000000000000000000000000 : ℝ)*base77 + (2160717704176101917/346375000000000000000000000000000 : ℝ)*base80 + (102206110952739/13855000000000000000000000000 : ℝ)*base81 + (6638341/1000000000000000000000 : ℝ)*base90 + (6638341/1000000000000000000000 : ℝ)*base92 + (6638341/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1071_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1071_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1071_s8_0 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2201310369/10000000000 : ℝ)*x 0 + (2697132627/5000000000 : ℝ)*x 1 + (5264547551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201310369/10000000000 : ℝ)^1033 ≤ (13369431769087/100000000000000 : ℝ)^777 := by
    have hnat : (2201310369 : ℕ)^1033*100000000000000^777 ≤ 13369431769087^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201310369 10000000000 13369431769087 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697132627/5000000000 : ℝ)^1033 ≤ (11004021161621/25000000000000 : ℝ)^777 := by
    have hnat : (2697132627 : ℕ)^1033*25000000000000^777 ≤ 11004021161621^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697132627 5000000000 11004021161621 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264547551/10000000000 : ℝ)^1033 ≤ (21307241781603/50000000000000 : ℝ)^777 := by
    have hnat : (5264547551 : ℕ)^1033*50000000000000^777 ≤ 21307241781603^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264547551 10000000000 21307241781603 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2201310369/10000000000 : ℝ), (2697132627/5000000000 : ℝ), (5264547551/10000000000 : ℝ)] ![(13369431769087/100000000000000 : ℝ), (11004021161621/25000000000000 : ℝ), (21307241781603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2201310369/10000000000 : ℝ)|^1033 ≤ (13369431769087/100000000000000 : ℝ)^777
        have hw : |(-2201310369/10000000000 : ℝ)|=(2201310369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697132627/5000000000 : ℝ)|^1033 ≤ (11004021161621/25000000000000 : ℝ)^777
        have hw : |(2697132627/5000000000 : ℝ)|=(2697132627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264547551/10000000000 : ℝ)|^1033 ≤ (21307241781603/50000000000000 : ℝ)^777
        have hw : |(5264547551/10000000000 : ℝ)|=(5264547551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s8_1 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344965877/10000000000 : ℝ)*x 0 + (-2267123663/10000000000 : ℝ)*x 1 + (2632273769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344965877/10000000000 : ℝ)^1033 ≤ (43482081087129/100000000000000 : ℝ)^777 := by
    have hnat : (5344965877 : ℕ)^1033*100000000000000^777 ≤ 43482081087129^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344965877 10000000000 43482081087129 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2267123663/10000000000 : ℝ)^1033 ≤ (3475858870391/25000000000000 : ℝ)^777 := by
    have hnat : (2267123663 : ℕ)^1033*25000000000000^777 ≤ 3475858870391^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267123663 10000000000 3475858870391 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632273769/5000000000 : ℝ)^1033 ≤ (21307241711653/50000000000000 : ℝ)^777 := by
    have hnat : (2632273769 : ℕ)^1033*50000000000000^777 ≤ 21307241711653^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632273769 5000000000 21307241711653 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344965877/10000000000 : ℝ), (-2267123663/10000000000 : ℝ), (2632273769/5000000000 : ℝ)] ![(43482081087129/100000000000000 : ℝ), (3475858870391/25000000000000 : ℝ), (21307241711653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344965877/10000000000 : ℝ)|^1033 ≤ (43482081087129/100000000000000 : ℝ)^777
        have hw : |(5344965877/10000000000 : ℝ)|=(5344965877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2267123663/10000000000 : ℝ)|^1033 ≤ (3475858870391/25000000000000 : ℝ)^777
        have hw : |(-2267123663/10000000000 : ℝ)|=(2267123663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632273769/5000000000 : ℝ)|^1033 ≤ (21307241711653/50000000000000 : ℝ)^777
        have hw : |(2632273769/5000000000 : ℝ)|=(2632273769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s8_2 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (42759727/80000000 : ℝ)*x 0 + (1052909509/2000000000 : ℝ)*x 1 + (-2267123657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42759727/80000000 : ℝ)^1033 ≤ (21741040532749/50000000000000 : ℝ)^777 := by
    have hnat : (42759727 : ℕ)^1033*50000000000000^777 ≤ 21741040532749^777*80000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42759727 80000000 21741040532749 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052909509/2000000000 : ℝ)^1033 ≤ (42614483498637/100000000000000 : ℝ)^777 := by
    have hnat : (1052909509 : ℕ)^1033*100000000000000^777 ≤ 42614483498637^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052909509 2000000000 42614483498637 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2267123657/10000000000 : ℝ)^1033 ≤ (2780687086529/20000000000000 : ℝ)^777 := by
    have hnat : (2267123657 : ℕ)^1033*20000000000000^777 ≤ 2780687086529^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267123657 10000000000 2780687086529 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42759727/80000000 : ℝ), (1052909509/2000000000 : ℝ), (-2267123657/10000000000 : ℝ)] ![(21741040532749/50000000000000 : ℝ), (42614483498637/100000000000000 : ℝ), (2780687086529/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42759727/80000000 : ℝ)|^1033 ≤ (21741040532749/50000000000000 : ℝ)^777
        have hw : |(42759727/80000000 : ℝ)|=(42759727/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052909509/2000000000 : ℝ)|^1033 ≤ (42614483498637/100000000000000 : ℝ)^777
        have hw : |(1052909509/2000000000 : ℝ)|=(1052909509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2267123657/10000000000 : ℝ)|^1033 ≤ (2780687086529/20000000000000 : ℝ)^777
        have hw : |(-2267123657/10000000000 : ℝ)|=(2267123657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s8_3 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (21873869/50000000 : ℝ)*x 0 + (4249405713/10000000000 : ℝ)*x 1 + (2251943383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21873869/50000000 : ℝ)^1033 ≤ (16658289788481/50000000000000 : ℝ)^777 := by
    have hnat : (21873869 : ℕ)^1033*50000000000000^777 ≤ 16658289788481^777*50000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21873869 50000000 16658289788481 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4249405713/10000000000 : ℝ)^1033 ≤ (16026645370349/50000000000000 : ℝ)^777 := by
    have hnat : (4249405713 : ℕ)^1033*50000000000000^777 ≤ 16026645370349^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249405713 10000000000 16026645370349 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251943383/5000000000 : ℝ)^1033 ≤ (8657532417903/25000000000000 : ℝ)^777 := by
    have hnat : (2251943383 : ℕ)^1033*25000000000000^777 ≤ 8657532417903^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251943383 5000000000 8657532417903 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21873869/50000000 : ℝ), (4249405713/10000000000 : ℝ), (2251943383/5000000000 : ℝ)] ![(16658289788481/50000000000000 : ℝ), (16026645370349/50000000000000 : ℝ), (8657532417903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21873869/50000000 : ℝ)|^1033 ≤ (16658289788481/50000000000000 : ℝ)^777
        have hw : |(21873869/50000000 : ℝ)|=(21873869/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4249405713/10000000000 : ℝ)|^1033 ≤ (16026645370349/50000000000000 : ℝ)^777
        have hw : |(4249405713/10000000000 : ℝ)|=(4249405713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251943383/5000000000 : ℝ)|^1033 ≤ (8657532417903/25000000000000 : ℝ)^777
        have hw : |(2251943383/5000000000 : ℝ)|=(2251943383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s8_4 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2201315443/10000000000 : ℝ)*x 0 + (5264872347/10000000000 : ℝ)*x 1 + (5393939269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201315443/10000000000 : ℝ)^1033 ≤ (3342368184669/25000000000000 : ℝ)^777 := by
    have hnat : (2201315443 : ℕ)^1033*25000000000000^777 ≤ 3342368184669^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201315443 10000000000 3342368184669 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264872347/10000000000 : ℝ)^1033 ≤ (4261797891237/10000000000000 : ℝ)^777 := by
    have hnat : (5264872347 : ℕ)^1033*10000000000000^777 ≤ 4261797891237^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264872347 10000000000 4261797891237 10000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393939269/10000000000 : ℝ)^1033 ≤ (1760501933011/4000000000000 : ℝ)^777 := by
    have hnat : (5393939269 : ℕ)^1033*4000000000000^777 ≤ 1760501933011^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393939269 10000000000 1760501933011 4000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2201315443/10000000000 : ℝ), (5264872347/10000000000 : ℝ), (5393939269/10000000000 : ℝ)] ![(3342368184669/25000000000000 : ℝ), (4261797891237/10000000000000 : ℝ), (1760501933011/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2201315443/10000000000 : ℝ)|^1033 ≤ (3342368184669/25000000000000 : ℝ)^777
        have hw : |(-2201315443/10000000000 : ℝ)|=(2201315443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264872347/10000000000 : ℝ)|^1033 ≤ (4261797891237/10000000000000 : ℝ)^777
        have hw : |(5264872347/10000000000 : ℝ)|=(5264872347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393939269/10000000000 : ℝ)|^1033 ≤ (1760501933011/4000000000000 : ℝ)^777
        have hw : |(5393939269/10000000000 : ℝ)|=(5393939269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s8_5 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (531227981/1000000000 : ℝ)*x 0 + (-534432843/2500000000 : ℝ)*x 1 + (5393939393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531227981/1000000000 : ℝ)^1033 ≤ (43128923110237/100000000000000 : ℝ)^777 := by
    have hnat : (531227981 : ℕ)^1033*100000000000000^777 ≤ 43128923110237^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531227981 1000000000 43128923110237 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534432843/2500000000 : ℝ)^1033 ≤ (2571705439791/20000000000000 : ℝ)^777 := by
    have hnat : (534432843 : ℕ)^1033*20000000000000^777 ≤ 2571705439791^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534432843 2500000000 2571705439791 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393939393/10000000000 : ℝ)^1033 ≤ (44012549670427/100000000000000 : ℝ)^777 := by
    have hnat : (5393939393 : ℕ)^1033*100000000000000^777 ≤ 44012549670427^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393939393 10000000000 44012549670427 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531227981/1000000000 : ℝ), (-534432843/2500000000 : ℝ), (5393939393/10000000000 : ℝ)] ![(43128923110237/100000000000000 : ℝ), (2571705439791/20000000000000 : ℝ), (44012549670427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531227981/1000000000 : ℝ)|^1033 ≤ (43128923110237/100000000000000 : ℝ)^777
        have hw : |(531227981/1000000000 : ℝ)|=(531227981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534432843/2500000000 : ℝ)|^1033 ≤ (2571705439791/20000000000000 : ℝ)^777
        have hw : |(-534432843/2500000000 : ℝ)|=(534432843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393939393/10000000000 : ℝ)|^1033 ≤ (44012549670427/100000000000000 : ℝ)^777
        have hw : |(5393939393/10000000000 : ℝ)|=(5393939393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s8_6 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312278901/10000000000 : ℝ)*x 0 + (1078787861/2000000000 : ℝ)*x 1 + (-1068866359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312278901/10000000000 : ℝ)^1033 ≤ (1078222832471/2500000000000 : ℝ)^777 := by
    have hnat : (5312278901 : ℕ)^1033*2500000000000^777 ≤ 1078222832471^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312278901 10000000000 1078222832471 2500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078787861/2000000000 : ℝ)^1033 ≤ (44012548715803/100000000000000 : ℝ)^777 := by
    have hnat : (1078787861 : ℕ)^1033*100000000000000^777 ≤ 44012548715803^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078787861 2000000000 44012548715803 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1068866359/5000000000 : ℝ)^1033 ≤ (6429268981339/50000000000000 : ℝ)^777 := by
    have hnat : (1068866359 : ℕ)^1033*50000000000000^777 ≤ 6429268981339^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068866359 5000000000 6429268981339 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312278901/10000000000 : ℝ), (1078787861/2000000000 : ℝ), (-1068866359/5000000000 : ℝ)] ![(1078222832471/2500000000000 : ℝ), (44012548715803/100000000000000 : ℝ), (6429268981339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312278901/10000000000 : ℝ)|^1033 ≤ (1078222832471/2500000000000 : ℝ)^777
        have hw : |(5312278901/10000000000 : ℝ)|=(5312278901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078787861/2000000000 : ℝ)|^1033 ≤ (44012548715803/100000000000000 : ℝ)^777
        have hw : |(1078787861/2000000000 : ℝ)|=(1078787861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1068866359/5000000000 : ℝ)|^1033 ≤ (6429268981339/50000000000000 : ℝ)^777
        have hw : |(-1068866359/5000000000 : ℝ)|=(1068866359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s8_7 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4374782977/10000000000 : ℝ)*x 0 + (56290617/125000000 : ℝ)*x 1 + (850009231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374782977/10000000000 : ℝ)^1033 ≤ (16658336245891/50000000000000 : ℝ)^777 := by
    have hnat : (4374782977 : ℕ)^1033*50000000000000^777 ≤ 16658336245891^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374782977 10000000000 16658336245891 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56290617/125000000 : ℝ)^1033 ≤ (6924722821631/20000000000000 : ℝ)^777 := by
    have hnat : (56290617 : ℕ)^1033*20000000000000^777 ≤ 6924722821631^777*125000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56290617 125000000 6924722821631 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850009231/2000000000 : ℝ)^1033 ≤ (4007464173947/12500000000000 : ℝ)^777 := by
    have hnat : (850009231 : ℕ)^1033*12500000000000^777 ≤ 4007464173947^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850009231 2000000000 4007464173947 12500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374782977/10000000000 : ℝ), (56290617/125000000 : ℝ), (850009231/2000000000 : ℝ)] ![(16658336245891/50000000000000 : ℝ), (6924722821631/20000000000000 : ℝ), (4007464173947/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374782977/10000000000 : ℝ)|^1033 ≤ (16658336245891/50000000000000 : ℝ)^777
        have hw : |(4374782977/10000000000 : ℝ)|=(4374782977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56290617/125000000 : ℝ)|^1033 ≤ (6924722821631/20000000000000 : ℝ)^777
        have hw : |(56290617/125000000 : ℝ)|=(56290617/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850009231/2000000000 : ℝ)|^1033 ≤ (4007464173947/12500000000000 : ℝ)^777
        have hw : |(850009231/2000000000 : ℝ)|=(850009231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1071_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5629/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7003/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1751/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1407/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1751/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1407/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1751/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1407/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1751/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1407/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1751/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1407/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1751/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1407/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1407/12500 : ℝ) ^ (8263/2048 : ℝ) ≤ (14881604240750059/100000000000000000000 : ℝ) := by
    have hpowers : (1407/12500 : ℝ)^8263 ≤ (14881604240750059/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1407 : ℕ)^8263*100000000000000000000^2048 ≤ 14881604240750059^2048*12500^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1407 12500 14881604240750059 100000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1407/12500 : ℝ)) (X := (14881604240750059/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1751/12500 : ℝ) ^ (8263/2048 : ℝ) ≤ (17983786211562351/50000000000000000000 : ℝ) := by
    have hpowers : (1751/12500 : ℝ)^8263 ≤ (17983786211562351/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1751 : ℕ)^8263*50000000000000000000^2048 ≤ 17983786211562351^2048*12500^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1751 12500 17983786211562351 50000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1751/12500 : ℝ)) (X := (17983786211562351/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014881604240750059/50000000000000000000 : ℝ) ≤ (5000368802065551/5000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (50014881604240750059/50000000000000000000 : ℝ)^2048 ≤ (5000368802065551/5000000000000000 : ℝ)^8263 := by
      have hnat : (50014881604240750059 : ℕ)^2048*5000000000000000^8263 ≤ 5000368802065551^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014881604240750059 50000000000000000000 5000368802065551 5000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000368802065551/5000000000000000 : ℝ)) (X := (50014881604240750059/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050849176663874761/100000000000000000000 : ℝ) ≤ (10001260065413751/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (100050849176663874761/100000000000000000000 : ℝ)^2048 ≤ (10001260065413751/10000000000000000 : ℝ)^8263 := by
      have hnat : (100050849176663874761 : ℕ)^2048*10000000000000000^8263 ≤ 10001260065413751^8263*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050849176663874761 100000000000000000000 10001260065413751 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001260065413751/10000000000000000 : ℝ)) (X := (100050849176663874761/100000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017983786211562351/25000000000000000000 : ℝ) ≤ (25004456316741/25000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (25017983786211562351/25000000000000000000 : ℝ)^2048 ≤ (25004456316741/25000000000000 : ℝ)^8263 := by
      have hnat : (25017983786211562351 : ℕ)^2048*25000000000000^8263 ≤ 25004456316741^8263*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017983786211562351 25000000000000000000 25004456316741 25000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25004456316741/25000000000000 : ℝ)) (X := (25017983786211562351/25000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14881604240750059/100000000000000000000 : ℝ) ≤ ((1719391764885862401/1720000000000000000 : ℝ)+2*(522461282649/275200000000000 : ℝ)*(1407/12500 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (1719391764885862401/1720000000000000000 : ℝ)+2*(522461282649/275200000000000 : ℝ)*(1407/12500 : ℝ)=(5000368802065551/5000000000000000 : ℝ) by norm_num, show 1+2*(14881604240750059/100000000000000000000 : ℝ)=(50014881604240750059/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17983786211562351/50000000000000000000 : ℝ)+(14881604240750059/100000000000000000000 : ℝ) ≤ ((1719391764885862401/1720000000000000000 : ℝ)+(522461282649/275200000000000 : ℝ)*((1751/12500 : ℝ)+(1407/12500 : ℝ)))^(8263/2048 : ℝ) := by
    rw [show (1719391764885862401/1720000000000000000 : ℝ)+(522461282649/275200000000000 : ℝ)*((1751/12500 : ℝ)+(1407/12500 : ℝ))=(10001260065413751/10000000000000000 : ℝ) by norm_num, show 1+(17983786211562351/50000000000000000000 : ℝ)+(14881604240750059/100000000000000000000 : ℝ)=(100050849176663874761/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17983786211562351/50000000000000000000 : ℝ) ≤ ((1719391764885862401/1720000000000000000 : ℝ)+2*(522461282649/275200000000000 : ℝ)*(1751/12500 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (1719391764885862401/1720000000000000000 : ℝ)+2*(522461282649/275200000000000 : ℝ)*(1751/12500 : ℝ)=(25004456316741/25000000000000 : ℝ) by norm_num, show 1+2*(17983786211562351/50000000000000000000 : ℝ)=(25017983786211562351/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1719391764885862401/1720000000000000000 : ℝ)*(X 1 0+X 2 0)+(522461282649/275200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (1407/12500 : ℝ)) (hi := (1751/12500 : ℝ)) (c := (1719391764885862401/1720000000000000000 : ℝ)) (alpha := (522461282649/275200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1719391764885862401/1720000000000000000 : ℝ)*(X 0 1+X 2 1)+(522461282649/275200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (1407/12500 : ℝ)) (hi := (1751/12500 : ℝ)) (c := (1719391764885862401/1720000000000000000 : ℝ)) (alpha := (522461282649/275200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1719391764885862401/1720000000000000000 : ℝ)*(X 0 2+X 1 2)+(522461282649/275200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (1407/12500 : ℝ)) (hi := (1751/12500 : ℝ)) (c := (1719391764885862401/1720000000000000000 : ℝ)) (alpha := (522461282649/275200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2201310369/10000000000 : ℝ)*X 0 0+(2697132627/5000000000 : ℝ)*X 0 1+(5264547551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344965877/10000000000 : ℝ)*X 1 0+(-2267123663/10000000000 : ℝ)*X 1 1+(2632273769/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42759727/80000000 : ℝ)*X 2 0+(1052909509/2000000000 : ℝ)*X 2 1+(-2267123657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((21873869/50000000 : ℝ)*X 0 0+(4249405713/10000000000 : ℝ)*X 0 1+(2251943383/5000000000 : ℝ)*X 0 2+(21873869/50000000 : ℝ)*X 1 0+(4249405713/10000000000 : ℝ)*X 1 1+(2251943383/5000000000 : ℝ)*X 1 2+(21873869/50000000 : ℝ)*X 2 0+(4249405713/10000000000 : ℝ)*X 2 1+(2251943383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2201315443/10000000000 : ℝ)*X 0 0+(5264872347/10000000000 : ℝ)*X 0 1+(5393939269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531227981/1000000000 : ℝ)*X 1 0+(-534432843/2500000000 : ℝ)*X 1 1+(5393939393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312278901/10000000000 : ℝ)*X 2 0+(1078787861/2000000000 : ℝ)*X 2 1+(-1068866359/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4374782977/10000000000 : ℝ)*X 0 0+(56290617/125000000 : ℝ)*X 0 1+(850009231/2000000000 : ℝ)*X 0 2+(4374782977/10000000000 : ℝ)*X 1 0+(56290617/125000000 : ℝ)*X 1 1+(850009231/2000000000 : ℝ)*X 1 2+(4374782977/10000000000 : ℝ)*X 2 0+(56290617/125000000 : ℝ)*X 2 1+(850009231/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10794517227503673099992601/1075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1003915767/50000000000000 : ℝ)*(base19) + (233930801/12500000000000 : ℝ)*(base23) + (71355553/100000000000000 : ℝ)*(lower2) + (242295277/100000000000000 : ℝ)*(upper3) + (152227547/100000000000000 : ℝ)*(upper5) + (1163878103927589/20000000000000 : ℝ)*(major0) + (1163878103927589/20000000000000 : ℝ)*(major1) + (1163878103927589/20000000000000 : ℝ)*(major2) + (7709104100324129/100000000000000 : ℝ)*(sp0) + (7709156074455881/100000000000000 : ℝ)*(sp1) + (7709156210841007/100000000000000 : ℝ)*(sp2) + (1964796399763683/50000000000000 : ℝ)*(sp3) + (53981963287/100000000000000 : ℝ)*(sp4) + (29822747389/100000000000000 : ℝ)*(sp7) + (785924524454951/20000000000000 : ℝ)*(f.failure) + (1541831616457483/20000000000000 : ℝ)*(f.sum) + (1614272101789/2752000000000000000000000000 : ℝ)*base65 + (311095949123862439/34400000000000000000000000000000 : ℝ)*base67 + (162152494771862439/34400000000000000000000000000000 : ℝ)*base69 + (127201146811062439/34400000000000000000000000000000 : ℝ)*base71 + (5180650040221/2752000000000000000000000000 : ℝ)*base73 + (853269282829462439/34400000000000000000000000000000 : ℝ)*base75 + (52255122823862439/34400000000000000000000000000000 : ℝ)*base77 + (35970448300137561/34400000000000000000000000000000 : ℝ)*base80 + (27928728439843/2752000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (620087/400000000000000000000 : ℝ)*base90 + (620087/400000000000000000000 : ℝ)*base92 + (620087/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (183729703648144176369450267/21500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126145409/12500000000000 : ℝ)*(base19) + (120375793/100000000000000 : ℝ)*(upper1) + (80137439/25000000000000 : ℝ)*(upper2) + (3842389/6250000000000 : ℝ)*(upper3) + (7397993/10000000000000 : ℝ)*(lower4) + (1462166003298989/25000000000000 : ℝ)*(major0) + (1462166003298989/25000000000000 : ℝ)*(major1) + (1462166003298989/25000000000000 : ℝ)*(major2) + (5336276423/25000000000000 : ℝ)*(sp0) + (3462299491/5000000000000 : ℝ)*(sp1) + (7747916449362833/100000000000000 : ℝ)*(sp4) + (7747867539315433/100000000000000 : ℝ)*(sp5) + (309917511778741/4000000000000 : ℝ)*(sp6) + (49367374338389/1250000000000 : ℝ)*(sp7) + (49367374338389/1250000000000 : ℝ)*(f.failure) + (309917511778741/4000000000000 : ℝ)*(f.sum) + (52958466818741/3440000000000000000000000000 : ℝ)*base65 + (205564966613956161/43000000000000000000000000000000 : ℝ)*base68 + (407798479463956161/43000000000000000000000000000000 : ℝ)*base70 + (838835541473043839/43000000000000000000000000000000 : ℝ)*base71 + (5084555825701/3440000000000000000000000000 : ℝ)*base73 + (62210315743956161/43000000000000000000000000000000 : ℝ)*base76 + (110870861808043839/43000000000000000000000000000000 : ℝ)*base77 + (465214889771956161/43000000000000000000000000000000 : ℝ)*base80 + (39325166225861/3440000000000000000000000000 : ℝ)*base81 + (279493/25000000000000000000 : ℝ)*base90 + (279493/25000000000000000000 : ℝ)*base92 + (279493/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1071_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1071_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1071_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1071_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1071_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1071_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1071_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
