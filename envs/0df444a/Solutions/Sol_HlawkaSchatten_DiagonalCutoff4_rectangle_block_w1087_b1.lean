-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1087_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:55:09.232113+00:00
-- url     : https://prove2.me/submissions/7459bb6c-9f8d-4ff4-a36d-7a106cdc8d21

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
theorem support_rectangle_w1087_s3_0 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-109450551/500000000 : ℝ)*x 0 + (5435111369/10000000000 : ℝ)*x 1 + (261331299/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109450551/500000000 : ℝ)^1035 ≤ (13287276638089/100000000000000 : ℝ)^779 := by
    have hnat : (109450551 : ℕ)^1035*100000000000000^779 ≤ 13287276638089^779*500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109450551 500000000 13287276638089 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435111369/10000000000 : ℝ)^1035 ≤ (44482679625047/100000000000000 : ℝ)^779 := by
    have hnat : (5435111369 : ℕ)^1035*100000000000000^779 ≤ 44482679625047^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435111369 10000000000 44482679625047 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261331299/500000000 : ℝ)^1035 ≤ (42230043719437/100000000000000 : ℝ)^779 := by
    have hnat : (261331299 : ℕ)^1035*100000000000000^779 ≤ 42230043719437^779*500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261331299 500000000 42230043719437 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109450551/500000000 : ℝ), (5435111369/10000000000 : ℝ), (261331299/500000000 : ℝ)] ![(13287276638089/100000000000000 : ℝ), (44482679625047/100000000000000 : ℝ), (42230043719437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109450551/500000000 : ℝ)|^1035 ≤ (13287276638089/100000000000000 : ℝ)^779
        have hw : |(-109450551/500000000 : ℝ)|=(109450551/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435111369/10000000000 : ℝ)|^1035 ≤ (44482679625047/100000000000000 : ℝ)^779
        have hw : |(5435111369/10000000000 : ℝ)|=(5435111369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261331299/500000000 : ℝ)|^1035 ≤ (42230043719437/100000000000000 : ℝ)^779
        have hw : |(261331299/500000000 : ℝ)|=(261331299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s3_1 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (334696931/625000000 : ℝ)*x 0 + (-1147858377/5000000000 : ℝ)*x 1 + (5226625921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334696931/625000000 : ℝ)^1035 ≤ (272595663381/625000000000 : ℝ)^779 := by
    have hnat : (334696931 : ℕ)^1035*625000000000^779 ≤ 272595663381^779*625000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334696931 625000000 272595663381 625000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1147858377/5000000000 : ℝ)^1035 ≤ (14154650756387/100000000000000 : ℝ)^779 := by
    have hnat : (1147858377 : ℕ)^1035*100000000000000^779 ≤ 14154650756387^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147858377 5000000000 14154650756387 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226625921/10000000000 : ℝ)^1035 ≤ (4223004308607/10000000000000 : ℝ)^779 := by
    have hnat : (5226625921 : ℕ)^1035*10000000000000^779 ≤ 4223004308607^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226625921 10000000000 4223004308607 10000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334696931/625000000 : ℝ), (-1147858377/5000000000 : ℝ), (5226625921/10000000000 : ℝ)] ![(272595663381/625000000000 : ℝ), (14154650756387/100000000000000 : ℝ), (4223004308607/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334696931/625000000 : ℝ)|^1035 ≤ (272595663381/625000000000 : ℝ)^779
        have hw : |(334696931/625000000 : ℝ)|=(334696931/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1147858377/5000000000 : ℝ)|^1035 ≤ (14154650756387/100000000000000 : ℝ)^779
        have hw : |(-1147858377/5000000000 : ℝ)|=(1147858377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226625921/10000000000 : ℝ)|^1035 ≤ (4223004308607/10000000000000 : ℝ)^779
        have hw : |(5226625921/10000000000 : ℝ)|=(5226625921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s3_2 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5355150801/10000000000 : ℝ)*x 0 + (5226626351/10000000000 : ℝ)*x 1 + (-2295716317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355150801/10000000000 : ℝ)^1035 ≤ (43615305112959/100000000000000 : ℝ)^779 := by
    have hnat : (5355150801 : ℕ)^1035*100000000000000^779 ≤ 43615305112959^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355150801 10000000000 43615305112959 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5226626351/10000000000 : ℝ)^1035 ≤ (42230047702131/100000000000000 : ℝ)^779 := by
    have hnat : (5226626351 : ℕ)^1035*100000000000000^779 ≤ 42230047702131^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226626351 10000000000 42230047702131 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2295716317/10000000000 : ℝ)^1035 ≤ (7077323588267/50000000000000 : ℝ)^779 := by
    have hnat : (2295716317 : ℕ)^1035*50000000000000^779 ≤ 7077323588267^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295716317 10000000000 7077323588267 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355150801/10000000000 : ℝ), (5226626351/10000000000 : ℝ), (-2295716317/10000000000 : ℝ)] ![(43615305112959/100000000000000 : ℝ), (42230047702131/100000000000000 : ℝ), (7077323588267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355150801/10000000000 : ℝ)|^1035 ≤ (43615305112959/100000000000000 : ℝ)^779
        have hw : |(5355150801/10000000000 : ℝ)|=(5355150801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5226626351/10000000000 : ℝ)|^1035 ≤ (42230047702131/100000000000000 : ℝ)^779
        have hw : |(5226626351/10000000000 : ℝ)|=(5226626351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2295716317/10000000000 : ℝ)|^1035 ≤ (7077323588267/50000000000000 : ℝ)^779
        have hw : |(-2295716317/10000000000 : ℝ)|=(2295716317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s3_3 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2184920481/5000000000 : ℝ)*x 0 + (2084767537/5000000000 : ℝ)*x 1 + (4579840547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184920481/5000000000 : ℝ)^1035 ≤ (33289949030689/100000000000000 : ℝ)^779 := by
    have hnat : (2184920481 : ℕ)^1035*100000000000000^779 ≤ 33289949030689^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184920481 5000000000 33289949030689 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084767537/5000000000 : ℝ)^1035 ≤ (3127795717561/10000000000000 : ℝ)^779 := by
    have hnat : (2084767537 : ℕ)^1035*10000000000000^779 ≤ 3127795717561^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084767537 5000000000 3127795717561 10000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4579840547/10000000000 : ℝ)^1035 ≤ (17716046891259/50000000000000 : ℝ)^779 := by
    have hnat : (4579840547 : ℕ)^1035*50000000000000^779 ≤ 17716046891259^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4579840547 10000000000 17716046891259 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184920481/5000000000 : ℝ), (2084767537/5000000000 : ℝ), (4579840547/10000000000 : ℝ)] ![(33289949030689/100000000000000 : ℝ), (3127795717561/10000000000000 : ℝ), (17716046891259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184920481/5000000000 : ℝ)|^1035 ≤ (33289949030689/100000000000000 : ℝ)^779
        have hw : |(2184920481/5000000000 : ℝ)|=(2184920481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084767537/5000000000 : ℝ)|^1035 ≤ (3127795717561/10000000000000 : ℝ)^779
        have hw : |(2084767537/5000000000 : ℝ)|=(2084767537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4579840547/10000000000 : ℝ)|^1035 ≤ (17716046891259/50000000000000 : ℝ)^779
        have hw : |(4579840547/10000000000 : ℝ)|=(4579840547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s3_4 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2189032173/10000000000 : ℝ)*x 0 + (2613733763/5000000000 : ℝ)*x 1 + (2717132419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189032173/10000000000 : ℝ)^1035 ≤ (13287447232021/100000000000000 : ℝ)^779 := by
    have hnat : (2189032173 : ℕ)^1035*100000000000000^779 ≤ 13287447232021^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189032173 10000000000 13287447232021 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613733763/5000000000 : ℝ)^1035 ≤ (21119538987269/50000000000000 : ℝ)^779 := by
    have hnat : (2613733763 : ℕ)^1035*50000000000000^779 ≤ 21119538987269^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613733763 5000000000 21119538987269 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717132419/5000000000 : ℝ)^1035 ≤ (44473474766111/100000000000000 : ℝ)^779 := by
    have hnat : (2717132419 : ℕ)^1035*100000000000000^779 ≤ 44473474766111^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717132419 5000000000 44473474766111 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2189032173/10000000000 : ℝ), (2613733763/5000000000 : ℝ), (2717132419/5000000000 : ℝ)] ![(13287447232021/100000000000000 : ℝ), (21119538987269/50000000000000 : ℝ), (44473474766111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2189032173/10000000000 : ℝ)|^1035 ≤ (13287447232021/100000000000000 : ℝ)^779
        have hw : |(-2189032173/10000000000 : ℝ)|=(2189032173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613733763/5000000000 : ℝ)|^1035 ≤ (21119538987269/50000000000000 : ℝ)^779
        have hw : |(2613733763/5000000000 : ℝ)|=(2613733763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717132419/5000000000 : ℝ)|^1035 ≤ (44473474766111/100000000000000 : ℝ)^779
        have hw : |(2717132419/5000000000 : ℝ)|=(2717132419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s3_5 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5302548743/10000000000 : ℝ)*x 0 + (-2088077691/10000000000 : ℝ)*x 1 + (1358566283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302548743/10000000000 : ℝ)^1035 ≤ (1721880617263/4000000000000 : ℝ)^779 := by
    have hnat : (5302548743 : ℕ)^1035*4000000000000^779 ≤ 1721880617263^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302548743 10000000000 1721880617263 4000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2088077691/10000000000 : ℝ)^1035 ≤ (12479506597723/100000000000000 : ℝ)^779 := by
    have hnat : (2088077691 : ℕ)^1035*100000000000000^779 ≤ 12479506597723^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088077691 10000000000 12479506597723 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358566283/2500000000 : ℝ)^1035 ≤ (355787823703/800000000000 : ℝ)^779 := by
    have hnat : (1358566283 : ℕ)^1035*800000000000^779 ≤ 355787823703^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358566283 2500000000 355787823703 800000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302548743/10000000000 : ℝ), (-2088077691/10000000000 : ℝ), (1358566283/2500000000 : ℝ)] ![(1721880617263/4000000000000 : ℝ), (12479506597723/100000000000000 : ℝ), (355787823703/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302548743/10000000000 : ℝ)|^1035 ≤ (1721880617263/4000000000000 : ℝ)^779
        have hw : |(5302548743/10000000000 : ℝ)|=(5302548743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2088077691/10000000000 : ℝ)|^1035 ≤ (12479506597723/100000000000000 : ℝ)^779
        have hw : |(-2088077691/10000000000 : ℝ)|=(2088077691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358566283/2500000000 : ℝ)|^1035 ≤ (355787823703/800000000000 : ℝ)^779
        have hw : |(1358566283/2500000000 : ℝ)|=(1358566283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s3_6 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2651274451/5000000000 : ℝ)*x 0 + (5434264867/10000000000 : ℝ)*x 1 + (-2088077837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651274451/5000000000 : ℝ)^1035 ≤ (5380877143319/12500000000000 : ℝ)^779 := by
    have hnat : (2651274451 : ℕ)^1035*12500000000000^779 ≤ 5380877143319^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651274451 5000000000 5380877143319 12500000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434264867/10000000000 : ℝ)^1035 ≤ (22236737540719/50000000000000 : ℝ)^779 := by
    have hnat : (5434264867 : ℕ)^1035*50000000000000^779 ≤ 22236737540719^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434264867 10000000000 22236737540719 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2088077837/10000000000 : ℝ)^1035 ≤ (3119876939263/25000000000000 : ℝ)^779 := by
    have hnat : (2088077837 : ℕ)^1035*25000000000000^779 ≤ 3119876939263^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088077837 10000000000 3119876939263 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651274451/5000000000 : ℝ), (5434264867/10000000000 : ℝ), (-2088077837/10000000000 : ℝ)] ![(5380877143319/12500000000000 : ℝ), (22236737540719/50000000000000 : ℝ), (3119876939263/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651274451/5000000000 : ℝ)|^1035 ≤ (5380877143319/12500000000000 : ℝ)^779
        have hw : |(2651274451/5000000000 : ℝ)|=(2651274451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434264867/10000000000 : ℝ)|^1035 ≤ (22236737540719/50000000000000 : ℝ)^779
        have hw : |(5434264867/10000000000 : ℝ)|=(5434264867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2088077837/10000000000 : ℝ)|^1035 ≤ (3119876939263/25000000000000 : ℝ)^779
        have hw : |(-2088077837/10000000000 : ℝ)|=(2088077837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s3_7 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (34959057/80000000 : ℝ)*x 0 + (4578185283/10000000000 : ℝ)*x 1 + (260700011/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34959057/80000000 : ℝ)^1035 ≤ (16645182833963/50000000000000 : ℝ)^779 := by
    have hnat : (34959057 : ℕ)^1035*50000000000000^779 ≤ 16645182833963^779*80000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34959057 80000000 16645182833963 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4578185283/10000000000 : ℝ)^1035 ≤ (35415080393723/100000000000000 : ℝ)^779 := by
    have hnat : (4578185283 : ℕ)^1035*100000000000000^779 ≤ 35415080393723^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578185283 10000000000 35415080393723 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260700011/625000000 : ℝ)^1035 ≤ (31294553922777/100000000000000 : ℝ)^779 := by
    have hnat : (260700011 : ℕ)^1035*100000000000000^779 ≤ 31294553922777^779*625000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260700011 625000000 31294553922777 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34959057/80000000 : ℝ), (4578185283/10000000000 : ℝ), (260700011/625000000 : ℝ)] ![(16645182833963/50000000000000 : ℝ), (35415080393723/100000000000000 : ℝ), (31294553922777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34959057/80000000 : ℝ)|^1035 ≤ (16645182833963/50000000000000 : ℝ)^779
        have hw : |(34959057/80000000 : ℝ)|=(34959057/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4578185283/10000000000 : ℝ)|^1035 ≤ (35415080393723/100000000000000 : ℝ)^779
        have hw : |(4578185283/10000000000 : ℝ)|=(4578185283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260700011/625000000 : ℝ)|^1035 ≤ (31294553922777/100000000000000 : ℝ)^779
        have hw : |(260700011/625000000 : ℝ)|=(260700011/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1087_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (521/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2093/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3719/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (521/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4407/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (521/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4407/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (521/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4407/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (521/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4407/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (521/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4407/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (521/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4407/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4407/50000 : ℝ) ^ (8279/2048 : ℝ) ≤ (5443555325778833/100000000000000000000 : ℝ) := by
    have hpowers : (4407/50000 : ℝ)^8279 ≤ (5443555325778833/100000000000000000000 : ℝ)^2048 := by
      have hnat : (4407 : ℕ)^8279*100000000000000000000^2048 ≤ 5443555325778833^2048*50000^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4407 50000 5443555325778833 100000000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4407/50000 : ℝ)) (X := (5443555325778833/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (521/3125 : ℝ) ^ (8279/2048 : ℝ) ≤ (71597932133828743/100000000000000000000 : ℝ) := by
    have hpowers : (521/3125 : ℝ)^8279 ≤ (71597932133828743/100000000000000000000 : ℝ)^2048 := by
      have hnat : (521 : ℕ)^8279*100000000000000000000^2048 ≤ 71597932133828743^2048*3125^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        521 3125 71597932133828743 100000000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (521/3125 : ℝ)) (X := (71597932133828743/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005443555325778833/50000000000000000000 : ℝ) ≤ (1250033663318607/1250000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (50005443555325778833/50000000000000000000 : ℝ)^2048 ≤ (1250033663318607/1250000000000000 : ℝ)^8279 := by
      have hnat : (50005443555325778833 : ℕ)^2048*1250000000000000^8279 ≤ 1250033663318607^8279*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005443555325778833 50000000000000000000 1250033663318607 1250000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250033663318607/1250000000000000 : ℝ)) (X := (50005443555325778833/50000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12509630185932450947/12500000000000000000 : ℝ) ≤ (10001905245119227/10000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (12509630185932450947/12500000000000000000 : ℝ)^2048 ≤ (10001905245119227/10000000000000000 : ℝ)^8279 := by
      have hnat : (12509630185932450947 : ℕ)^2048*10000000000000000^8279 ≤ 10001905245119227^8279*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509630185932450947 12500000000000000000 10001905245119227 10000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001905245119227/10000000000000000 : ℝ)) (X := (12509630185932450947/12500000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50071597932133828743/50000000000000000000 : ℝ) ≤ (5001770591844799/5000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (50071597932133828743/50000000000000000000 : ℝ)^2048 ≤ (5001770591844799/5000000000000000 : ℝ)^8279 := by
      have hnat : (50071597932133828743 : ℕ)^2048*5000000000000000^8279 ≤ 5001770591844799^8279*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50071597932133828743 50000000000000000000 5001770591844799 5000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001770591844799/5000000000000000 : ℝ)) (X := (50071597932133828743/50000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5443555325778833/100000000000000000000 : ℝ) ≤ ((3927663894287120523/3929000000000000000 : ℝ)+2*(1635938570371/785800000000000 : ℝ)*(4407/50000 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (3927663894287120523/3929000000000000000 : ℝ)+2*(1635938570371/785800000000000 : ℝ)*(4407/50000 : ℝ)=(1250033663318607/1250000000000000 : ℝ) by norm_num, show 1+2*(5443555325778833/100000000000000000000 : ℝ)=(50005443555325778833/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(71597932133828743/100000000000000000000 : ℝ)+(5443555325778833/100000000000000000000 : ℝ) ≤ ((3927663894287120523/3929000000000000000 : ℝ)+(1635938570371/785800000000000 : ℝ)*((521/3125 : ℝ)+(4407/50000 : ℝ)))^(8279/2048 : ℝ) := by
    rw [show (3927663894287120523/3929000000000000000 : ℝ)+(1635938570371/785800000000000 : ℝ)*((521/3125 : ℝ)+(4407/50000 : ℝ))=(10001905245119227/10000000000000000 : ℝ) by norm_num, show 1+(71597932133828743/100000000000000000000 : ℝ)+(5443555325778833/100000000000000000000 : ℝ)=(12509630185932450947/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(71597932133828743/100000000000000000000 : ℝ) ≤ ((3927663894287120523/3929000000000000000 : ℝ)+2*(1635938570371/785800000000000 : ℝ)*(521/3125 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (3927663894287120523/3929000000000000000 : ℝ)+2*(1635938570371/785800000000000 : ℝ)*(521/3125 : ℝ)=(5001770591844799/5000000000000000 : ℝ) by norm_num, show 1+2*(71597932133828743/100000000000000000000 : ℝ)=(50071597932133828743/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3927663894287120523/3929000000000000000 : ℝ)*(X 1 0+X 2 0)+(1635938570371/785800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (4407/50000 : ℝ)) (hi := (521/3125 : ℝ)) (c := (3927663894287120523/3929000000000000000 : ℝ)) (alpha := (1635938570371/785800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3927663894287120523/3929000000000000000 : ℝ)*(X 0 1+X 2 1)+(1635938570371/785800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (4407/50000 : ℝ)) (hi := (521/3125 : ℝ)) (c := (3927663894287120523/3929000000000000000 : ℝ)) (alpha := (1635938570371/785800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3927663894287120523/3929000000000000000 : ℝ)*(X 0 2+X 1 2)+(1635938570371/785800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (4407/50000 : ℝ)) (hi := (521/3125 : ℝ)) (c := (3927663894287120523/3929000000000000000 : ℝ)) (alpha := (1635938570371/785800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-109450551/500000000 : ℝ)*X 0 0+(5435111369/10000000000 : ℝ)*X 0 1+(261331299/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334696931/625000000 : ℝ)*X 1 0+(-1147858377/5000000000 : ℝ)*X 1 1+(5226625921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355150801/10000000000 : ℝ)*X 2 0+(5226626351/10000000000 : ℝ)*X 2 1+(-2295716317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184920481/5000000000 : ℝ)*X 0 0+(2084767537/5000000000 : ℝ)*X 0 1+(4579840547/10000000000 : ℝ)*X 0 2+(2184920481/5000000000 : ℝ)*X 1 0+(2084767537/5000000000 : ℝ)*X 1 1+(4579840547/10000000000 : ℝ)*X 1 2+(2184920481/5000000000 : ℝ)*X 2 0+(2084767537/5000000000 : ℝ)*X 2 1+(4579840547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2189032173/10000000000 : ℝ)*X 0 0+(2613733763/5000000000 : ℝ)*X 0 1+(2717132419/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302548743/10000000000 : ℝ)*X 1 0+(-2088077691/10000000000 : ℝ)*X 1 1+(1358566283/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651274451/5000000000 : ℝ)*X 2 0+(5434264867/10000000000 : ℝ)*X 2 1+(-2088077837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((34959057/80000000 : ℝ)*X 0 0+(4578185283/10000000000 : ℝ)*X 0 1+(260700011/625000000 : ℝ)*X 0 2+(34959057/80000000 : ℝ)*X 1 0+(4578185283/10000000000 : ℝ)*X 1 1+(260700011/625000000 : ℝ)*X 1 2+(34959057/80000000 : ℝ)*X 2 0+(4578185283/10000000000 : ℝ)*X 2 1+(260700011/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8733194968267269341583987/1964500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1343919767/100000000000000 : ℝ)*(base19) + (4455043/500000000000 : ℝ)*(base23) + (196973553/100000000000000 : ℝ)*(lower2) + (8921131/50000000000000 : ℝ)*(upper3) + (153516921/100000000000000 : ℝ)*(upper5) + (36168888338959/1000000000000 : ℝ)*(major0) + (36168888338959/1000000000000 : ℝ)*(major1) + (36168888338959/1000000000000 : ℝ)*(major2) + (1199130162231619/25000000000000 : ℝ)*(sp0) + (2398273988964271/50000000000000 : ℝ)*(sp1) + (1199137107709927/25000000000000 : ℝ)*(sp2) + (1218609346543209/50000000000000 : ℝ)*(sp3) + (3584115229/12500000000000 : ℝ)*(sp4) + (594042097/6250000000000 : ℝ)*(sp7) + (243722819775997/10000000000000 : ℝ)*(f.failure) + (1199137330462077/25000000000000 : ℝ)*(f.sum) + (25839095359/15716000000000000000000000 : ℝ)*base65 + (66059989965404557/3929000000000000000000000000000 : ℝ)*base67 + (49675933962374557/3929000000000000000000000000000 : ℝ)*base69 + (75427149024408557/3929000000000000000000000000000 : ℝ)*base71 + (1654110920897/392900000000000000000000000 : ℝ)*base73 + (8141109689880557/3929000000000000000000000000000 : ℝ)*base75 + (53882349926204557/3929000000000000000000000000000 : ℝ)*base77 + (29831418705876557/3929000000000000000000000000000 : ℝ)*base79 + (104927870551/491125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (12949193/1000000000000000000000 : ℝ)*base90 + (12949193/1000000000000000000000 : ℝ)*base92 + (12949193/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (594659513970038544675326133/98225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (276234631/25000000000000 : ℝ)*(base19) + (294647897/20000000000000 : ℝ)*(base23) + (207722081/100000000000000 : ℝ)*(upper3) + (4768393/5000000000000 : ℝ)*(lower4) + (8734911/25000000000000 : ℝ)*(upper5) + (3646370819308143/100000000000000 : ℝ)*(major0) + (3646370819308143/100000000000000 : ℝ)*(major1) + (3646370819308143/100000000000000 : ℝ)*(major2) + (4227829333/20000000000000 : ℝ)*(sp1) + (25519082391/100000000000000 : ℝ)*(sp2) + (4835646903794389/100000000000000 : ℝ)*(sp4) + (12089061649273/250000000000 : ℝ)*(sp5) + (4835619911472513/100000000000000 : ℝ)*(sp6) + (76784204156877/3125000000000 : ℝ)*(sp7) + (76784204156877/3125000000000 : ℝ)*(f.failure) + (4835646903794389/100000000000000 : ℝ)*(f.sum) + (25144533409817/39290000000000000000000000000 : ℝ)*base66 + (2693627529326183789/392900000000000000000000000000000 : ℝ)*base67 + (3779565599518183789/392900000000000000000000000000000 : ℝ)*base69 + (886408007904416211/392900000000000000000000000000000 : ℝ)*base72 + (103127226957473/39290000000000000000000000000 : ℝ)*base73 + (7313731005887483789/392900000000000000000000000000000 : ℝ)*base75 + (1862210978482283789/392900000000000000000000000000000 : ℝ)*base77 + (2263687118351983789/392900000000000000000000000000000 : ℝ)*base79 + (139473328075613/39290000000000000000000000000 : ℝ)*base81 + (4520913/312500000000000000000 : ℝ)*base90 + (4520913/312500000000000000000 : ℝ)*base92 + (4520913/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1087_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (521/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2093/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3719/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1087_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1087_s4_0 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2192487773/10000000000 : ℝ)*x 0 + (5404668791/10000000000 : ℝ)*x 1 + (1313699111/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2192487773/10000000000 : ℝ)^1035 ≤ (13315323097529/100000000000000 : ℝ)^779 := by
    have hnat : (2192487773 : ℕ)^1035*100000000000000^779 ≤ 13315323097529^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192487773 10000000000 13315323097529 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404668791/10000000000 : ℝ)^1035 ≤ (5518994384729/12500000000000 : ℝ)^779 := by
    have hnat : (5404668791 : ℕ)^1035*12500000000000^779 ≤ 5518994384729^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404668791 10000000000 5518994384729 12500000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313699111/2500000000 : ℝ)^1035 ≤ (10633180452539/25000000000000 : ℝ)^779 := by
    have hnat : (1313699111 : ℕ)^1035*25000000000000^779 ≤ 10633180452539^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313699111 2500000000 10633180452539 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2192487773/10000000000 : ℝ), (5404668791/10000000000 : ℝ), (1313699111/2500000000 : ℝ)] ![(13315323097529/100000000000000 : ℝ), (5518994384729/12500000000000 : ℝ), (10633180452539/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2192487773/10000000000 : ℝ)|^1035 ≤ (13315323097529/100000000000000 : ℝ)^779
        have hw : |(-2192487773/10000000000 : ℝ)|=(2192487773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404668791/10000000000 : ℝ)|^1035 ≤ (5518994384729/12500000000000 : ℝ)^779
        have hw : |(5404668791/10000000000 : ℝ)|=(5404668791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313699111/2500000000 : ℝ)|^1035 ≤ (10633180452539/25000000000000 : ℝ)^779
        have hw : |(1313699111/2500000000 : ℝ)|=(1313699111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s4_1 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (267379637/500000000 : ℝ)*x 0 + (-1134348309/5000000000 : ℝ)*x 1 + (2627398511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267379637/500000000 : ℝ)^1035 ≤ (43533537798171/100000000000000 : ℝ)^779 := by
    have hnat : (267379637 : ℕ)^1035*100000000000000^779 ≤ 43533537798171^779*500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267379637 500000000 43533537798171 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134348309/5000000000 : ℝ)^1035 ≤ (6966867081003/50000000000000 : ℝ)^779 := by
    have hnat : (1134348309 : ℕ)^1035*50000000000000^779 ≤ 6966867081003^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134348309 5000000000 6966867081003 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627398511/5000000000 : ℝ)^1035 ≤ (4253272802597/10000000000000 : ℝ)^779 := by
    have hnat : (2627398511 : ℕ)^1035*10000000000000^779 ≤ 4253272802597^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627398511 5000000000 4253272802597 10000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267379637/500000000 : ℝ), (-1134348309/5000000000 : ℝ), (2627398511/5000000000 : ℝ)] ![(43533537798171/100000000000000 : ℝ), (6966867081003/50000000000000 : ℝ), (4253272802597/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267379637/500000000 : ℝ)|^1035 ≤ (43533537798171/100000000000000 : ℝ)^779
        have hw : |(267379637/500000000 : ℝ)|=(267379637/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1134348309/5000000000 : ℝ)|^1035 ≤ (6966867081003/50000000000000 : ℝ)^779
        have hw : |(-1134348309/5000000000 : ℝ)|=(1134348309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627398511/5000000000 : ℝ)|^1035 ≤ (4253272802597/10000000000000 : ℝ)^779
        have hw : |(2627398511/5000000000 : ℝ)|=(2627398511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s4_2 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673796531/5000000000 : ℝ)*x 0 + (1313699187/2500000000 : ℝ)*x 1 + (-2268696553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673796531/5000000000 : ℝ)^1035 ≤ (21766770640469/50000000000000 : ℝ)^779 := by
    have hnat : (2673796531 : ℕ)^1035*50000000000000^779 ≤ 21766770640469^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673796531 5000000000 21766770640469 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313699187/2500000000 : ℝ)^1035 ≤ (42532725079373/100000000000000 : ℝ)^779 := by
    have hnat : (1313699187 : ℕ)^1035*100000000000000^779 ≤ 42532725079373^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313699187 2500000000 42532725079373 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2268696553/10000000000 : ℝ)^1035 ≤ (6966866815801/50000000000000 : ℝ)^779 := by
    have hnat : (2268696553 : ℕ)^1035*50000000000000^779 ≤ 6966866815801^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268696553 10000000000 6966866815801 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673796531/5000000000 : ℝ), (1313699187/2500000000 : ℝ), (-2268696553/10000000000 : ℝ)] ![(21766770640469/50000000000000 : ℝ), (42532725079373/100000000000000 : ℝ), (6966866815801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673796531/5000000000 : ℝ)|^1035 ≤ (21766770640469/50000000000000 : ℝ)^779
        have hw : |(2673796531/5000000000 : ℝ)|=(2673796531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313699187/2500000000 : ℝ)|^1035 ≤ (42532725079373/100000000000000 : ℝ)^779
        have hw : |(1313699187/2500000000 : ℝ)|=(1313699187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2268696553/10000000000 : ℝ)|^1035 ≤ (6966866815801/50000000000000 : ℝ)^779
        have hw : |(-2268696553/10000000000 : ℝ)|=(2268696553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s4_3 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (273244449/625000000 : ℝ)*x 0 + (2113470233/5000000000 : ℝ)*x 1 + (226094687/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273244449/625000000 : ℝ)^1035 ≤ (33310904679551/100000000000000 : ℝ)^779 := by
    have hnat : (273244449 : ℕ)^1035*100000000000000^779 ≤ 33310904679551^779*625000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273244449 625000000 33310904679551 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113470233/5000000000 : ℝ)^1035 ≤ (31851392828623/100000000000000 : ℝ)^779 := by
    have hnat : (2113470233 : ℕ)^1035*100000000000000^779 ≤ 31851392828623^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113470233 5000000000 31851392828623 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226094687/500000000 : ℝ)^1035 ≤ (34837702469321/100000000000000 : ℝ)^779 := by
    have hnat : (226094687 : ℕ)^1035*100000000000000^779 ≤ 34837702469321^779*500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226094687 500000000 34837702469321 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273244449/625000000 : ℝ), (2113470233/5000000000 : ℝ), (226094687/500000000 : ℝ)] ![(33310904679551/100000000000000 : ℝ), (31851392828623/100000000000000 : ℝ), (34837702469321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273244449/625000000 : ℝ)|^1035 ≤ (33310904679551/100000000000000 : ℝ)^779
        have hw : |(273244449/625000000 : ℝ)|=(273244449/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113470233/5000000000 : ℝ)|^1035 ≤ (31851392828623/100000000000000 : ℝ)^779
        have hw : |(2113470233/5000000000 : ℝ)|=(2113470233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226094687/500000000 : ℝ)|^1035 ≤ (34837702469321/100000000000000 : ℝ)^779
        have hw : |(226094687/500000000 : ℝ)|=(226094687/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s4_4 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2192494681/10000000000 : ℝ)*x 0 + (1051046529/2000000000 : ℝ)*x 1 + (1080846291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2192494681/10000000000 : ℝ)^1035 ≤ (3328844709479/25000000000000 : ℝ)^779 := by
    have hnat : (2192494681 : ℕ)^1035*25000000000000^779 ≤ 3328844709479^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192494681 10000000000 3328844709479 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051046529/2000000000 : ℝ)^1035 ≤ (42537412781183/100000000000000 : ℝ)^779 := by
    have hnat : (1051046529 : ℕ)^1035*100000000000000^779 ≤ 42537412781183^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051046529 2000000000 42537412781183 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080846291/2000000000 : ℝ)^1035 ≤ (22073604181177/50000000000000 : ℝ)^779 := by
    have hnat : (1080846291 : ℕ)^1035*50000000000000^779 ≤ 22073604181177^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080846291 2000000000 22073604181177 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2192494681/10000000000 : ℝ), (1051046529/2000000000 : ℝ), (1080846291/2000000000 : ℝ)] ![(3328844709479/25000000000000 : ℝ), (42537412781183/100000000000000 : ℝ), (22073604181177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2192494681/10000000000 : ℝ)|^1035 ≤ (3328844709479/25000000000000 : ℝ)^779
        have hw : |(-2192494681/10000000000 : ℝ)|=(2192494681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051046529/2000000000 : ℝ)|^1035 ≤ (42537412781183/100000000000000 : ℝ)^779
        have hw : |(1051046529/2000000000 : ℝ)|=(1051046529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080846291/2000000000 : ℝ)|^1035 ≤ (22073604181177/50000000000000 : ℝ)^779
        have hw : |(1080846291/2000000000 : ℝ)|=(1080846291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s4_5 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530978271/1000000000 : ℝ)*x 0 + (-2119261793/10000000000 : ℝ)*x 1 + (675528933/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530978271/1000000000 : ℝ)^1035 ≤ (8625011727601/20000000000000 : ℝ)^779 := by
    have hnat : (530978271 : ℕ)^1035*20000000000000^779 ≤ 8625011727601^779*1000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530978271 1000000000 8625011727601 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119261793/10000000000 : ℝ)^1035 ≤ (12727732889899/100000000000000 : ℝ)^779 := by
    have hnat : (2119261793 : ℕ)^1035*100000000000000^779 ≤ 12727732889899^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119261793 10000000000 12727732889899 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675528933/1250000000 : ℝ)^1035 ≤ (11036802115009/25000000000000 : ℝ)^779 := by
    have hnat : (675528933 : ℕ)^1035*25000000000000^779 ≤ 11036802115009^779*1250000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675528933 1250000000 11036802115009 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530978271/1000000000 : ℝ), (-2119261793/10000000000 : ℝ), (675528933/1250000000 : ℝ)] ![(8625011727601/20000000000000 : ℝ), (12727732889899/100000000000000 : ℝ), (11036802115009/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530978271/1000000000 : ℝ)|^1035 ≤ (8625011727601/20000000000000 : ℝ)^779
        have hw : |(530978271/1000000000 : ℝ)|=(530978271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2119261793/10000000000 : ℝ)|^1035 ≤ (12727732889899/100000000000000 : ℝ)^779
        have hw : |(-2119261793/10000000000 : ℝ)|=(2119261793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675528933/1250000000 : ℝ)|^1035 ≤ (11036802115009/25000000000000 : ℝ)^779
        have hw : |(675528933/1250000000 : ℝ)|=(675528933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s4_6 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5309782529/10000000000 : ℝ)*x 0 + (5404231477/10000000000 : ℝ)*x 1 + (-105963101/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309782529/10000000000 : ℝ)^1035 ≤ (43125056684861/100000000000000 : ℝ)^779 := by
    have hnat : (5309782529 : ℕ)^1035*100000000000000^779 ≤ 43125056684861^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309782529 10000000000 43125056684861 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404231477/10000000000 : ℝ)^1035 ≤ (11036802150283/25000000000000 : ℝ)^779 := by
    have hnat : (5404231477 : ℕ)^1035*25000000000000^779 ≤ 11036802150283^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404231477 10000000000 11036802150283 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105963101/500000000 : ℝ)^1035 ≤ (12727734701219/100000000000000 : ℝ)^779 := by
    have hnat : (105963101 : ℕ)^1035*100000000000000^779 ≤ 12727734701219^779*500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105963101 500000000 12727734701219 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309782529/10000000000 : ℝ), (5404231477/10000000000 : ℝ), (-105963101/500000000 : ℝ)] ![(43125056684861/100000000000000 : ℝ), (11036802150283/25000000000000 : ℝ), (12727734701219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309782529/10000000000 : ℝ)|^1035 ≤ (43125056684861/100000000000000 : ℝ)^779
        have hw : |(5309782529/10000000000 : ℝ)|=(5309782529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404231477/10000000000 : ℝ)|^1035 ≤ (11036802150283/25000000000000 : ℝ)^779
        have hw : |(5404231477/10000000000 : ℝ)|=(5404231477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105963101/500000000 : ℝ)|^1035 ≤ (12727734701219/100000000000000 : ℝ)^779
        have hw : |(-105963101/500000000 : ℝ)|=(105963101/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s4_7 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2185963141/5000000000 : ℝ)*x 0 + (1130259119/2500000000 : ℝ)*x 1 + (4227801623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185963141/5000000000 : ℝ)^1035 ≤ (33311057519771/100000000000000 : ℝ)^779 := by
    have hnat : (2185963141 : ℕ)^1035*100000000000000^779 ≤ 33311057519771^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185963141 5000000000 33311057519771 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130259119/2500000000 : ℝ)^1035 ≤ (8707231938163/25000000000000 : ℝ)^779 := by
    have hnat : (1130259119 : ℕ)^1035*25000000000000^779 ≤ 8707231938163^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130259119 2500000000 8707231938163 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227801623/10000000000 : ℝ)^1035 ≤ (7965003677597/25000000000000 : ℝ)^779 := by
    have hnat : (4227801623 : ℕ)^1035*25000000000000^779 ≤ 7965003677597^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227801623 10000000000 7965003677597 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185963141/5000000000 : ℝ), (1130259119/2500000000 : ℝ), (4227801623/10000000000 : ℝ)] ![(33311057519771/100000000000000 : ℝ), (8707231938163/25000000000000 : ℝ), (7965003677597/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185963141/5000000000 : ℝ)|^1035 ≤ (33311057519771/100000000000000 : ℝ)^779
        have hw : |(2185963141/5000000000 : ℝ)|=(2185963141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130259119/2500000000 : ℝ)|^1035 ≤ (8707231938163/25000000000000 : ℝ)^779
        have hw : |(1130259119/2500000000 : ℝ)|=(1130259119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227801623/10000000000 : ℝ)|^1035 ≤ (7965003677597/25000000000000 : ℝ)^779
        have hw : |(4227801623/10000000000 : ℝ)|=(4227801623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1087_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3719/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2093/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5533/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (89/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3719/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2093/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3719/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2093/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3719/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2093/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3719/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2093/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3719/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2093/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3719/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2093/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2093/20000 : ℝ) ^ (8279/2048 : ℝ) ≤ (5448600904327961/50000000000000000000 : ℝ) := by
    have hpowers : (2093/20000 : ℝ)^8279 ≤ (5448600904327961/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2093 : ℕ)^8279*50000000000000000000^2048 ≤ 5448600904327961^2048*20000^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2093 20000 5448600904327961 50000000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2093/20000 : ℝ)) (X := (5448600904327961/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3719/25000 : ℝ) ^ (8279/2048 : ℝ) ≤ (11290976721179133/25000000000000000000 : ℝ) := by
    have hpowers : (3719/25000 : ℝ)^8279 ≤ (11290976721179133/25000000000000000000 : ℝ)^2048 := by
      have hnat : (3719 : ℕ)^8279*25000000000000000000^2048 ≤ 11290976721179133^2048*25000^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3719 25000 11290976721179133 25000000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3719/25000 : ℝ)) (X := (11290976721179133/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005448600904327961/25000000000000000000 : ℝ) ≤ (2500134772552019/2500000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (25005448600904327961/25000000000000000000 : ℝ)^2048 ≤ (2500134772552019/2500000000000000 : ℝ)^8279 := by
      have hnat : (25005448600904327961 : ℕ)^2048*2500000000000000^8279 ≤ 2500134772552019^8279*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005448600904327961 25000000000000000000 2500134772552019 2500000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134772552019/2500000000000000 : ℝ)) (X := (25005448600904327961/25000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50028030554346686227/50000000000000000000 : ℝ) ≤ (312543328352199/312500000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (50028030554346686227/50000000000000000000 : ℝ)^2048 ≤ (312543328352199/312500000000000 : ℝ)^8279 := by
      have hnat : (50028030554346686227 : ℕ)^2048*312500000000000^8279 ≤ 312543328352199^8279*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028030554346686227 50000000000000000000 312543328352199 312500000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312543328352199/312500000000000 : ℝ)) (X := (50028030554346686227/50000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12511290976721179133/12500000000000000000 : ℝ) ≤ (500111696216633/500000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (12511290976721179133/12500000000000000000 : ℝ)^2048 ≤ (500111696216633/500000000000000 : ℝ)^8279 := by
      have hnat : (12511290976721179133 : ℕ)^2048*500000000000000^8279 ≤ 500111696216633^8279*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511290976721179133 12500000000000000000 500111696216633 500000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500111696216633/500000000000000 : ℝ)) (X := (12511290976721179133/12500000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5448600904327961/50000000000000000000 : ℝ) ≤ ((11023660371948512919/11027500000000000000 : ℝ)+2*(211854265573/110275000000000 : ℝ)*(2093/20000 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (11023660371948512919/11027500000000000000 : ℝ)+2*(211854265573/110275000000000 : ℝ)*(2093/20000 : ℝ)=(2500134772552019/2500000000000000 : ℝ) by norm_num, show 1+2*(5448600904327961/50000000000000000000 : ℝ)=(25005448600904327961/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11290976721179133/25000000000000000000 : ℝ)+(5448600904327961/50000000000000000000 : ℝ) ≤ ((11023660371948512919/11027500000000000000 : ℝ)+(211854265573/110275000000000 : ℝ)*((3719/25000 : ℝ)+(2093/20000 : ℝ)))^(8279/2048 : ℝ) := by
    rw [show (11023660371948512919/11027500000000000000 : ℝ)+(211854265573/110275000000000 : ℝ)*((3719/25000 : ℝ)+(2093/20000 : ℝ))=(312543328352199/312500000000000 : ℝ) by norm_num, show 1+(11290976721179133/25000000000000000000 : ℝ)+(5448600904327961/50000000000000000000 : ℝ)=(50028030554346686227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11290976721179133/25000000000000000000 : ℝ) ≤ ((11023660371948512919/11027500000000000000 : ℝ)+2*(211854265573/110275000000000 : ℝ)*(3719/25000 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (11023660371948512919/11027500000000000000 : ℝ)+2*(211854265573/110275000000000 : ℝ)*(3719/25000 : ℝ)=(500111696216633/500000000000000 : ℝ) by norm_num, show 1+2*(11290976721179133/25000000000000000000 : ℝ)=(12511290976721179133/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11023660371948512919/11027500000000000000 : ℝ)*(X 1 0+X 2 0)+(211854265573/110275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (2093/20000 : ℝ)) (hi := (3719/25000 : ℝ)) (c := (11023660371948512919/11027500000000000000 : ℝ)) (alpha := (211854265573/110275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11023660371948512919/11027500000000000000 : ℝ)*(X 0 1+X 2 1)+(211854265573/110275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (2093/20000 : ℝ)) (hi := (3719/25000 : ℝ)) (c := (11023660371948512919/11027500000000000000 : ℝ)) (alpha := (211854265573/110275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11023660371948512919/11027500000000000000 : ℝ)*(X 0 2+X 1 2)+(211854265573/110275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (2093/20000 : ℝ)) (hi := (3719/25000 : ℝ)) (c := (11023660371948512919/11027500000000000000 : ℝ)) (alpha := (211854265573/110275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2192487773/10000000000 : ℝ)*X 0 0+(5404668791/10000000000 : ℝ)*X 0 1+(1313699111/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267379637/500000000 : ℝ)*X 1 0+(-1134348309/5000000000 : ℝ)*X 1 1+(2627398511/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673796531/5000000000 : ℝ)*X 2 0+(1313699187/2500000000 : ℝ)*X 2 1+(-2268696553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((273244449/625000000 : ℝ)*X 0 0+(2113470233/5000000000 : ℝ)*X 0 1+(226094687/500000000 : ℝ)*X 0 2+(273244449/625000000 : ℝ)*X 1 0+(2113470233/5000000000 : ℝ)*X 1 1+(226094687/500000000 : ℝ)*X 1 2+(273244449/625000000 : ℝ)*X 2 0+(2113470233/5000000000 : ℝ)*X 2 1+(226094687/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2192494681/10000000000 : ℝ)*X 0 0+(1051046529/2000000000 : ℝ)*X 0 1+(1080846291/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530978271/1000000000 : ℝ)*X 1 0+(-2119261793/10000000000 : ℝ)*X 1 1+(675528933/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309782529/10000000000 : ℝ)*X 2 0+(5404231477/10000000000 : ℝ)*X 2 1+(-105963101/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185963141/5000000000 : ℝ)*X 0 0+(1130259119/2500000000 : ℝ)*X 0 1+(4227801623/10000000000 : ℝ)*X 0 2+(2185963141/5000000000 : ℝ)*X 1 0+(1130259119/2500000000 : ℝ)*X 1 1+(4227801623/10000000000 : ℝ)*X 1 2+(2185963141/5000000000 : ℝ)*X 2 0+(1130259119/2500000000 : ℝ)*X 2 1+(4227801623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73896634827557637206950689/13784375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2820135889/100000000000000 : ℝ)*(base19) + (1360361447/50000000000000 : ℝ)*(base23) + (62452721/12500000000000 : ℝ)*(upper3) + (134008317/50000000000000 : ℝ)*(upper4) + (60144163/20000000000000 : ℝ)*(upper5) + (15723356316697/312500000000 : ℝ)*(major0) + (15723356316697/312500000000 : ℝ)*(major1) + (15723356316697/312500000000 : ℝ)*(major2) + (1334484867819763/20000000000000 : ℝ)*(sp0) + (6672503444932433/100000000000000 : ℝ)*(sp1) + (6672503544345427/100000000000000 : ℝ)*(sp2) + (1695200357793341/50000000000000 : ℝ)*(sp3) + (40962984753/50000000000000 : ℝ)*(sp4) + (10220833613/25000000000000 : ℝ)*(sp7) + (1695220799460567/50000000000000 : ℝ)*(f.failure) + (6672506265068321/100000000000000 : ℝ)*(f.sum) + (296065051789/882200000000000000000000000 : ℝ)*base66 + (31803352847306453/13784375000000000000000000000000 : ℝ)*base68 + (89443800765586039/6892187500000000000000000000000 : ℝ)*base70 + (2136220624827709/1723046875000000000000000000000 : ℝ)*base71 + (4793212182767/2205500000000000000000000000 : ℝ)*base74 + (165237113894017289/6892187500000000000000000000000 : ℝ)*base76 + (34567756311929789/6892187500000000000000000000000 : ℝ)*base78 + (97159747748835207/3446093750000000000000000000000 : ℝ)*base80 + (25527953813059/4411000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9041477/5000000000000000000000 : ℝ)*base89 + (9041477/5000000000000000000000 : ℝ)*base91 + (9041477/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (866038435873039365251333223/110275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (767564031/50000000000000 : ℝ)*(base19) + (898468017/50000000000000 : ℝ)*(base23) + (77159729/100000000000000 : ℝ)*(upper3) + (260896917/100000000000000 : ℝ)*(lower4) + (21667999/25000000000000 : ℝ)*(upper5) + (1012168737828139/20000000000000 : ℝ)*(major0) + (1012168737828139/20000000000000 : ℝ)*(major1) + (1012168737828139/20000000000000 : ℝ)*(major2) + (42452723471/100000000000000 : ℝ)*(sp1) + (10586243409/25000000000000 : ℝ)*(sp2) + (6711454867160019/100000000000000 : ℝ)*(sp4) + (1342282175861697/20000000000000 : ℝ)*(sp5) + (6711410725250349/100000000000000 : ℝ)*(sp6) + (852558062334983/25000000000000 : ℝ)*(sp7) + (852558062334983/25000000000000 : ℝ)*(f.failure) + (6711454867160019/100000000000000 : ℝ)*(f.sum) + (14165120532147/4411000000000000000000000000 : ℝ)*base66 + (106163675369922259/220550000000000000000000000000000 : ℝ)*base68 + (515245857116622259/220550000000000000000000000000000 : ℝ)*base70 + (754685358385227741/220550000000000000000000000000000 : ℝ)*base71 + (39735815451/4411000000000000000000000000 : ℝ)*base74 + (780187666422972259/220550000000000000000000000000000 : ℝ)*base76 + (410324948385577741/220550000000000000000000000000000 : ℝ)*base77 + (344787956510222259/220550000000000000000000000000000 : ℝ)*base80 + (140443080101/110275000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4055573/2500000000000000000000 : ℝ)*base89 + (4055573/2500000000000000000000 : ℝ)*base91 + (4055573/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1087_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3719/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2093/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (89/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1087_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1087_s5_0 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2193258633/10000000000 : ℝ)*x 0 + (5396403763/10000000000 : ℝ)*x 1 + (5262555803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2193258633/10000000000 : ℝ)^1035 ≤ (333038587333/2500000000000 : ℝ)^779 := by
    have hnat : (2193258633 : ℕ)^1035*2500000000000^779 ≤ 333038587333^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193258633 10000000000 333038587333 2500000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396403763/10000000000 : ℝ)^1035 ≤ (22031135133361/50000000000000 : ℝ)^779 := by
    have hnat : (5396403763 : ℕ)^1035*50000000000000^779 ≤ 22031135133361^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396403763 10000000000 22031135133361 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262555803/10000000000 : ℝ)^1035 ≤ (4261618622267/10000000000000 : ℝ)^779 := by
    have hnat : (5262555803 : ℕ)^1035*10000000000000^779 ≤ 4261618622267^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262555803 10000000000 4261618622267 10000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2193258633/10000000000 : ℝ), (5396403763/10000000000 : ℝ), (5262555803/10000000000 : ℝ)] ![(333038587333/2500000000000 : ℝ), (22031135133361/50000000000000 : ℝ), (4261618622267/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2193258633/10000000000 : ℝ)|^1035 ≤ (333038587333/2500000000000 : ℝ)^779
        have hw : |(-2193258633/10000000000 : ℝ)|=(2193258633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396403763/10000000000 : ℝ)|^1035 ≤ (22031135133361/50000000000000 : ℝ)^779
        have hw : |(5396403763/10000000000 : ℝ)|=(5396403763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262555803/10000000000 : ℝ)|^1035 ≤ (4261618622267/10000000000000 : ℝ)^779
        have hw : |(5262555803/10000000000 : ℝ)|=(5262555803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s5_1 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672765163/5000000000 : ℝ)*x 0 + (-2261198797/10000000000 : ℝ)*x 1 + (526255553/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672765163/5000000000 : ℝ)^1035 ≤ (21755616023523/50000000000000 : ℝ)^779 := by
    have hnat : (2672765163 : ℕ)^1035*50000000000000^779 ≤ 21755616023523^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672765163 5000000000 21755616023523 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261198797/10000000000 : ℝ)^1035 ≤ (2774516930459/20000000000000 : ℝ)^779 := by
    have hnat : (2261198797 : ℕ)^1035*20000000000000^779 ≤ 2774516930459^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261198797 10000000000 2774516930459 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526255553/1000000000 : ℝ)^1035 ≤ (42616183285403/100000000000000 : ℝ)^779 := by
    have hnat : (526255553 : ℕ)^1035*100000000000000^779 ≤ 42616183285403^779*1000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526255553 1000000000 42616183285403 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672765163/5000000000 : ℝ), (-2261198797/10000000000 : ℝ), (526255553/1000000000 : ℝ)] ![(21755616023523/50000000000000 : ℝ), (2774516930459/20000000000000 : ℝ), (42616183285403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672765163/5000000000 : ℝ)|^1035 ≤ (21755616023523/50000000000000 : ℝ)^779
        have hw : |(2672765163/5000000000 : ℝ)|=(2672765163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2261198797/10000000000 : ℝ)|^1035 ≤ (2774516930459/20000000000000 : ℝ)^779
        have hw : |(-2261198797/10000000000 : ℝ)|=(2261198797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526255553/1000000000 : ℝ)|^1035 ≤ (42616183285403/100000000000000 : ℝ)^779
        have hw : |(526255553/1000000000 : ℝ)|=(526255553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s5_2 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5345530187/10000000000 : ℝ)*x 0 + (5262555939/10000000000 : ℝ)*x 1 + (-2261198441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345530187/10000000000 : ℝ)^1035 ≤ (21755615271903/50000000000000 : ℝ)^779 := by
    have hnat : (5345530187 : ℕ)^1035*50000000000000^779 ≤ 21755615271903^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345530187 10000000000 21755615271903 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262555939/10000000000 : ℝ)^1035 ≤ (10654046921481/25000000000000 : ℝ)^779 := by
    have hnat : (5262555939 : ℕ)^1035*25000000000000^779 ≤ 10654046921481^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262555939 10000000000 10654046921481 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261198441/10000000000 : ℝ)^1035 ≤ (3468145437617/25000000000000 : ℝ)^779 := by
    have hnat : (2261198441 : ℕ)^1035*25000000000000^779 ≤ 3468145437617^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261198441 10000000000 3468145437617 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345530187/10000000000 : ℝ), (5262555939/10000000000 : ℝ), (-2261198441/10000000000 : ℝ)] ![(21755615271903/50000000000000 : ℝ), (10654046921481/25000000000000 : ℝ), (3468145437617/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345530187/10000000000 : ℝ)|^1035 ≤ (21755615271903/50000000000000 : ℝ)^779
        have hw : |(5345530187/10000000000 : ℝ)|=(5345530187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262555939/10000000000 : ℝ)|^1035 ≤ (10654046921481/25000000000000 : ℝ)^779
        have hw : |(5262555939/10000000000 : ℝ)|=(5262555939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2261198441/10000000000 : ℝ)|^1035 ≤ (3468145437617/25000000000000 : ℝ)^779
        have hw : |(-2261198441/10000000000 : ℝ)|=(2261198441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s5_3 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4372359423/10000000000 : ℝ)*x 0 + (2121324863/5000000000 : ℝ)*x 1 + (4506067083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372359423/10000000000 : ℝ)^1035 ≤ (6663088474167/20000000000000 : ℝ)^779 := by
    have hnat : (4372359423 : ℕ)^1035*20000000000000^779 ≤ 6663088474167^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372359423 10000000000 6663088474167 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121324863/5000000000 : ℝ)^1035 ≤ (32008764234231/100000000000000 : ℝ)^779 := by
    have hnat : (2121324863 : ℕ)^1035*100000000000000^779 ≤ 32008764234231^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121324863 5000000000 32008764234231 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506067083/10000000000 : ℝ)^1035 ≤ (1733789669447/5000000000000 : ℝ)^779 := by
    have hnat : (4506067083 : ℕ)^1035*5000000000000^779 ≤ 1733789669447^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506067083 10000000000 1733789669447 5000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372359423/10000000000 : ℝ), (2121324863/5000000000 : ℝ), (4506067083/10000000000 : ℝ)] ![(6663088474167/20000000000000 : ℝ), (32008764234231/100000000000000 : ℝ), (1733789669447/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372359423/10000000000 : ℝ)|^1035 ≤ (6663088474167/20000000000000 : ℝ)^779
        have hw : |(4372359423/10000000000 : ℝ)|=(4372359423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2121324863/5000000000 : ℝ)|^1035 ≤ (32008764234231/100000000000000 : ℝ)^779
        have hw : |(2121324863/5000000000 : ℝ)|=(2121324863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506067083/10000000000 : ℝ)|^1035 ≤ (1733789669447/5000000000000 : ℝ)^779
        have hw : |(4506067083/10000000000 : ℝ)|=(4506067083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s5_4 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-137079013/625000000 : ℝ)*x 0 + (5262903409/10000000000 : ℝ)*x 1 + (269802743/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137079013/625000000 : ℝ)^1035 ≤ (13321588482973/100000000000000 : ℝ)^779 := by
    have hnat : (137079013 : ℕ)^1035*100000000000000^779 ≤ 13321588482973^779*625000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137079013 625000000 13321588482973 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262903409/10000000000 : ℝ)^1035 ≤ (8523985246489/20000000000000 : ℝ)^779 := by
    have hnat : (5262903409 : ℕ)^1035*20000000000000^779 ≤ 8523985246489^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262903409 10000000000 8523985246489 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269802743/500000000 : ℝ)^1035 ≤ (11014621317701/25000000000000 : ℝ)^779 := by
    have hnat : (269802743 : ℕ)^1035*25000000000000^779 ≤ 11014621317701^779*500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269802743 500000000 11014621317701 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-137079013/625000000 : ℝ), (5262903409/10000000000 : ℝ), (269802743/500000000 : ℝ)] ![(13321588482973/100000000000000 : ℝ), (8523985246489/20000000000000 : ℝ), (11014621317701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-137079013/625000000 : ℝ)|^1035 ≤ (13321588482973/100000000000000 : ℝ)^779
        have hw : |(-137079013/625000000 : ℝ)|=(137079013/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262903409/10000000000 : ℝ)|^1035 ≤ (8523985246489/20000000000000 : ℝ)^779
        have hw : |(5262903409/10000000000 : ℝ)|=(5262903409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269802743/500000000 : ℝ)|^1035 ≤ (11014621317701/25000000000000 : ℝ)^779
        have hw : |(269802743/500000000 : ℝ)|=(269802743/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s5_5 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5311761223/10000000000 : ℝ)*x 0 + (-212769963/1000000000 : ℝ)*x 1 + (1079210959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311761223/10000000000 : ℝ)^1035 ≤ (21573204895607/50000000000000 : ℝ)^779 := by
    have hnat : (5311761223 : ℕ)^1035*50000000000000^779 ≤ 21573204895607^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311761223 10000000000 21573204895607 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212769963/1000000000 : ℝ)^1035 ≤ (12795105635007/100000000000000 : ℝ)^779 := by
    have hnat : (212769963 : ℕ)^1035*100000000000000^779 ≤ 12795105635007^779*1000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212769963 1000000000 12795105635007 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079210959/2000000000 : ℝ)^1035 ≤ (44058484565673/100000000000000 : ℝ)^779 := by
    have hnat : (1079210959 : ℕ)^1035*100000000000000^779 ≤ 44058484565673^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079210959 2000000000 44058484565673 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311761223/10000000000 : ℝ), (-212769963/1000000000 : ℝ), (1079210959/2000000000 : ℝ)] ![(21573204895607/50000000000000 : ℝ), (12795105635007/100000000000000 : ℝ), (44058484565673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311761223/10000000000 : ℝ)|^1035 ≤ (21573204895607/50000000000000 : ℝ)^779
        have hw : |(5311761223/10000000000 : ℝ)|=(5311761223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212769963/1000000000 : ℝ)|^1035 ≤ (12795105635007/100000000000000 : ℝ)^779
        have hw : |(-212769963/1000000000 : ℝ)|=(212769963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079210959/2000000000 : ℝ)|^1035 ≤ (44058484565673/100000000000000 : ℝ)^779
        have hw : |(1079210959/2000000000 : ℝ)|=(1079210959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s5_6 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (212470449/400000000 : ℝ)*x 0 + (2698027411/5000000000 : ℝ)*x 1 + (-212769959/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212470449/400000000 : ℝ)^1035 ≤ (43146409812799/100000000000000 : ℝ)^779 := by
    have hnat : (212470449 : ℕ)^1035*100000000000000^779 ≤ 43146409812799^779*400000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212470449 400000000 43146409812799 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698027411/5000000000 : ℝ)^1035 ≤ (22029242429287/50000000000000 : ℝ)^779 := by
    have hnat : (2698027411 : ℕ)^1035*50000000000000^779 ≤ 22029242429287^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698027411 5000000000 22029242429287 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212769959/1000000000 : ℝ)^1035 ≤ (2559021063083/20000000000000 : ℝ)^779 := by
    have hnat : (212769959 : ℕ)^1035*20000000000000^779 ≤ 2559021063083^779*1000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212769959 1000000000 2559021063083 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212470449/400000000 : ℝ), (2698027411/5000000000 : ℝ), (-212769959/1000000000 : ℝ)] ![(43146409812799/100000000000000 : ℝ), (22029242429287/50000000000000 : ℝ), (2559021063083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212470449/400000000 : ℝ)|^1035 ≤ (43146409812799/100000000000000 : ℝ)^779
        have hw : |(212470449/400000000 : ℝ)|=(212470449/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698027411/5000000000 : ℝ)|^1035 ≤ (22029242429287/50000000000000 : ℝ)^779
        have hw : |(2698027411/5000000000 : ℝ)|=(2698027411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212769959/1000000000 : ℝ)|^1035 ≤ (2559021063083/20000000000000 : ℝ)^779
        have hw : |(-212769959/1000000000 : ℝ)|=(212769959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s5_7 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (174894803/400000000 : ℝ)*x 0 + (225269157/500000000 : ℝ)*x 1 + (1060834137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174894803/400000000 : ℝ)^1035 ≤ (208222188793/625000000000 : ℝ)^779 := by
    have hnat : (174894803 : ℕ)^1035*625000000000^779 ≤ 208222188793^779*400000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174894803 400000000 208222188793 625000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225269157/500000000 : ℝ)^1035 ≤ (34668800756139/100000000000000 : ℝ)^779 := by
    have hnat : (225269157 : ℕ)^1035*100000000000000^779 ≤ 34668800756139^779*500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225269157 500000000 34668800756139 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060834137/2500000000 : ℝ)^1035 ≤ (16007824509527/50000000000000 : ℝ)^779 := by
    have hnat : (1060834137 : ℕ)^1035*50000000000000^779 ≤ 16007824509527^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060834137 2500000000 16007824509527 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174894803/400000000 : ℝ), (225269157/500000000 : ℝ), (1060834137/2500000000 : ℝ)] ![(208222188793/625000000000 : ℝ), (34668800756139/100000000000000 : ℝ), (16007824509527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174894803/400000000 : ℝ)|^1035 ≤ (208222188793/625000000000 : ℝ)^779
        have hw : |(174894803/400000000 : ℝ)|=(174894803/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225269157/500000000 : ℝ)|^1035 ≤ (34668800756139/100000000000000 : ℝ)^779
        have hw : |(225269157/500000000 : ℝ)|=(225269157/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060834137/2500000000 : ℝ)|^1035 ≤ (16007824509527/50000000000000 : ℝ)^779
        have hw : |(1060834137/2500000000 : ℝ)|=(1060834137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1087_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (351/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14067/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5533/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5533/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5533/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5533/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5533/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5533/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5533/50000 : ℝ) ^ (8279/2048 : ℝ) ≤ (1707107820368779/12500000000000000000 : ℝ) := by
    have hpowers : (5533/50000 : ℝ)^8279 ≤ (1707107820368779/12500000000000000000 : ℝ)^2048 := by
      have hnat : (5533 : ℕ)^8279*12500000000000000000^2048 ≤ 1707107820368779^2048*50000^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5533 50000 1707107820368779 12500000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5533/50000 : ℝ)) (X := (1707107820368779/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (89/625 : ℝ) ^ (8279/2048 : ℝ) ≤ (4731411027651519/12500000000000000000 : ℝ) := by
    have hpowers : (89/625 : ℝ)^8279 ≤ (4731411027651519/12500000000000000000 : ℝ)^2048 := by
      have hnat : (89 : ℕ)^8279*12500000000000000000^2048 ≤ 4731411027651519^2048*625^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 625 4731411027651519 12500000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/625 : ℝ)) (X := (4731411027651519/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251707107820368779/6250000000000000000 : ℝ) ≤ (10000675598022967/10000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (6251707107820368779/6250000000000000000 : ℝ)^2048 ≤ (10000675598022967/10000000000000000 : ℝ)^8279 := by
      have hnat : (6251707107820368779 : ℕ)^2048*10000000000000000^8279 ≤ 10000675598022967^8279*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251707107820368779 6250000000000000000 10000675598022967 10000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000675598022967/10000000000000000 : ℝ)) (X := (6251707107820368779/6250000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253219259424010149/6250000000000000000 : ℝ) ≤ (2000254785002671/2000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (6253219259424010149/6250000000000000000 : ℝ)^2048 ≤ (2000254785002671/2000000000000000 : ℝ)^8279 := by
      have hnat : (6253219259424010149 : ℕ)^2048*2000000000000000^8279 ≤ 2000254785002671^8279*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253219259424010149 6250000000000000000 2000254785002671 2000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000254785002671/2000000000000000 : ℝ)) (X := (6253219259424010149/6250000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254731411027651519/6250000000000000000 : ℝ) ≤ (10001872252003743/10000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (6254731411027651519/6250000000000000000 : ℝ)^2048 ≤ (10001872252003743/10000000000000000 : ℝ)^8279 := by
      have hnat : (6254731411027651519 : ℕ)^2048*10000000000000000^8279 ≤ 10001872252003743^8279*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254731411027651519 6250000000000000000 10001872252003743 10000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001872252003743/10000000000000000 : ℝ)) (X := (6254731411027651519/6250000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1707107820368779/12500000000000000000 : ℝ) ≤ ((15864451087586815021/15870000000000000000 : ℝ)+2*(149581747597/79350000000000 : ℝ)*(5533/50000 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (15864451087586815021/15870000000000000000 : ℝ)+2*(149581747597/79350000000000 : ℝ)*(5533/50000 : ℝ)=(10000675598022967/10000000000000000 : ℝ) by norm_num, show 1+2*(1707107820368779/12500000000000000000 : ℝ)=(6251707107820368779/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4731411027651519/12500000000000000000 : ℝ)+(1707107820368779/12500000000000000000 : ℝ) ≤ ((15864451087586815021/15870000000000000000 : ℝ)+(149581747597/79350000000000 : ℝ)*((89/625 : ℝ)+(5533/50000 : ℝ)))^(8279/2048 : ℝ) := by
    rw [show (15864451087586815021/15870000000000000000 : ℝ)+(149581747597/79350000000000 : ℝ)*((89/625 : ℝ)+(5533/50000 : ℝ))=(2000254785002671/2000000000000000 : ℝ) by norm_num, show 1+(4731411027651519/12500000000000000000 : ℝ)+(1707107820368779/12500000000000000000 : ℝ)=(6253219259424010149/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4731411027651519/12500000000000000000 : ℝ) ≤ ((15864451087586815021/15870000000000000000 : ℝ)+2*(149581747597/79350000000000 : ℝ)*(89/625 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (15864451087586815021/15870000000000000000 : ℝ)+2*(149581747597/79350000000000 : ℝ)*(89/625 : ℝ)=(10001872252003743/10000000000000000 : ℝ) by norm_num, show 1+2*(4731411027651519/12500000000000000000 : ℝ)=(6254731411027651519/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15864451087586815021/15870000000000000000 : ℝ)*(X 1 0+X 2 0)+(149581747597/79350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (5533/50000 : ℝ)) (hi := (89/625 : ℝ)) (c := (15864451087586815021/15870000000000000000 : ℝ)) (alpha := (149581747597/79350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15864451087586815021/15870000000000000000 : ℝ)*(X 0 1+X 2 1)+(149581747597/79350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (5533/50000 : ℝ)) (hi := (89/625 : ℝ)) (c := (15864451087586815021/15870000000000000000 : ℝ)) (alpha := (149581747597/79350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15864451087586815021/15870000000000000000 : ℝ)*(X 0 2+X 1 2)+(149581747597/79350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (5533/50000 : ℝ)) (hi := (89/625 : ℝ)) (c := (15864451087586815021/15870000000000000000 : ℝ)) (alpha := (149581747597/79350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2193258633/10000000000 : ℝ)*X 0 0+(5396403763/10000000000 : ℝ)*X 0 1+(5262555803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672765163/5000000000 : ℝ)*X 1 0+(-2261198797/10000000000 : ℝ)*X 1 1+(526255553/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345530187/10000000000 : ℝ)*X 2 0+(5262555939/10000000000 : ℝ)*X 2 1+(-2261198441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4372359423/10000000000 : ℝ)*X 0 0+(2121324863/5000000000 : ℝ)*X 0 1+(4506067083/10000000000 : ℝ)*X 0 2+(4372359423/10000000000 : ℝ)*X 1 0+(2121324863/5000000000 : ℝ)*X 1 1+(4506067083/10000000000 : ℝ)*X 1 2+(4372359423/10000000000 : ℝ)*X 2 0+(2121324863/5000000000 : ℝ)*X 2 1+(4506067083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-137079013/625000000 : ℝ)*X 0 0+(5262903409/10000000000 : ℝ)*X 0 1+(269802743/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311761223/10000000000 : ℝ)*X 1 0+(-212769963/1000000000 : ℝ)*X 1 1+(1079210959/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212470449/400000000 : ℝ)*X 2 0+(2698027411/5000000000 : ℝ)*X 2 1+(-212769959/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174894803/400000000 : ℝ)*X 0 0+(225269157/500000000 : ℝ)*X 0 1+(1060834137/2500000000 : ℝ)*X 0 2+(174894803/400000000 : ℝ)*X 1 0+(225269157/500000000 : ℝ)*X 1 1+(1060834137/2500000000 : ℝ)*X 1 2+(174894803/400000000 : ℝ)*X 2 0+(225269157/500000000 : ℝ)*X 2 1+(1060834137/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (707156174260313523315013629/264500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (336736263/25000000000000 : ℝ)*(base19) + (810983239/100000000000000 : ℝ)*(base23) + (22973141/12500000000000 : ℝ)*(lower2) + (242317049/100000000000000 : ℝ)*(upper5) + (5633748351365649/100000000000000 : ℝ)*(major0) + (5633748351365649/100000000000000 : ℝ)*(major1) + (5633748351365649/100000000000000 : ℝ)*(major2) + (1867795414067801/25000000000000 : ℝ)*(sp0) + (1494242565935001/20000000000000 : ℝ)*(sp1) + (3735606850869141/50000000000000 : ℝ)*(sp2) + (3796271486957921/100000000000000 : ℝ)*(sp3) + (32856450317/100000000000000 : ℝ)*(sp4) + (336101463/100000000000000 : ℝ)*(sp5) + (265348331/2500000000000 : ℝ)*(sp7) + (3796282100891161/100000000000000 : ℝ)*(f.failure) + (7471214512721521/100000000000000 : ℝ)*(f.sum) + (2319829861873/2645000000000000000000000000 : ℝ)*base66 + (5233992677216595457/529000000000000000000000000000000 : ℝ)*base68 + (7560287551692595457/529000000000000000000000000000000 : ℝ)*base70 + (4227929321135595457/529000000000000000000000000000000 : ℝ)*base72 + (12548708904993/2645000000000000000000000000 : ℝ)*base74 + (192310443020404543/529000000000000000000000000000000 : ℝ)*base75 + (693967163569404543/529000000000000000000000000000000 : ℝ)*base77 + (880420803013595457/529000000000000000000000000000000 : ℝ)*base80 + (1145124754343/2645000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (34999691/10000000000000000000000 : ℝ)*base89 + (34999691/10000000000000000000000 : ℝ)*base91 + (34999691/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12655730720181052918083/1322500000000000000000000000 : ℝ) := by norm_num
    linear_combination (226817507/12500000000000 : ℝ)*(base19) + (2074326429/100000000000000 : ℝ)*(base23) + (90245127/50000000000000 : ℝ)*(upper3) + (22605867/20000000000000 : ℝ)*(lower4) + (42439373/20000000000000 : ℝ)*(upper5) + (707897361795183/12500000000000 : ℝ)*(major0) + (707897361795183/12500000000000 : ℝ)*(major1) + (707897361795183/12500000000000 : ℝ)*(major2) + (363206471/800000000000 : ℝ)*(sp1) + (26174241597/50000000000000 : ℝ)*(sp2) + (1877560924470849/25000000000000 : ℝ)*(sp4) + (1502039296506893/20000000000000 : ℝ)*(sp5) + (300407571002951/4000000000000 : ℝ)*(sp6) + (119253555370453/3125000000000 : ℝ)*(sp7) + (119253555370453/3125000000000 : ℝ)*(f.failure) + (1877560924470849/25000000000000 : ℝ)*(f.sum) + (468938567873/165312500000000000000000000 : ℝ)*base66 + (204293395477818719/66125000000000000000000000000000 : ℝ)*base68 + (1008668560652681281/66125000000000000000000000000000 : ℝ)*base69 + (605962233773556281/66125000000000000000000000000000 : ℝ)*base71 + (11289623639503/2645000000000000000000000000 : ℝ)*base74 + (1370951971329556281/66125000000000000000000000000000 : ℝ)*base75 + (59126832167943719/66125000000000000000000000000000 : ℝ)*base78 + (688856420266318719/66125000000000000000000000000000 : ℝ)*base80 + (2369569802273/661250000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base87 + (3545857/312500000000000000000 : ℝ)*base90 + (3545857/312500000000000000000 : ℝ)*base92 + (3545857/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1087_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1087_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1087_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (521/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1087_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1087_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1087_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (521/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1087_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
