-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1170_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:44:33.111602+00:00
-- url     : https://prove2.me/submissions/d7f5c704-d7dd-4c9d-9766-2fb51e615f5f

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
theorem support_rectangle_w1170_s0_0 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-9414901/50000000 : ℝ)*x 0 + (3023940643/5000000000 : ℝ)*x 1 + (1196000841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9414901/50000000 : ℝ)^8363 ≤ (219130586951/2000000000000 : ℝ)^6315 := by
    have hnat : (9414901 : ℕ)^8363*2000000000000^6315 ≤ 219130586951^6315*50000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9414901 50000000 219130586951 2000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3023940643/5000000000 : ℝ)^8363 ≤ (3211113364529/6250000000000 : ℝ)^6315 := by
    have hnat : (3023940643 : ℕ)^8363*6250000000000^6315 ≤ 3211113364529^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3023940643 5000000000 3211113364529 6250000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196000841/2500000000 : ℝ)^8363 ≤ (1883282840539/5000000000000 : ℝ)^6315 := by
    have hnat : (1196000841 : ℕ)^8363*5000000000000^6315 ≤ 1883282840539^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196000841 2500000000 1883282840539 5000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9414901/50000000 : ℝ), (3023940643/5000000000 : ℝ), (1196000841/2500000000 : ℝ)] ![(219130586951/2000000000000 : ℝ), (3211113364529/6250000000000 : ℝ), (1883282840539/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9414901/50000000 : ℝ)|^8363 ≤ (219130586951/2000000000000 : ℝ)^6315
        have hw : |(-9414901/50000000 : ℝ)|=(9414901/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3023940643/5000000000 : ℝ)|^8363 ≤ (3211113364529/6250000000000 : ℝ)^6315
        have hw : |(3023940643/5000000000 : ℝ)|=(3023940643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1196000841/2500000000 : ℝ)|^8363 ≤ (1883282840539/5000000000000 : ℝ)^6315
        have hw : |(1196000841/2500000000 : ℝ)|=(1196000841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s0_1 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1378804039/2500000000 : ℝ)*x 0 + (-521501667/2000000000 : ℝ)*x 1 + (1196000839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378804039/2500000000 : ℝ)^8363 ≤ (22736280141259/50000000000000 : ℝ)^6315 := by
    have hnat : (1378804039 : ℕ)^8363*50000000000000^6315 ≤ 22736280141259^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378804039 2500000000 22736280141259 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521501667/2000000000 : ℝ)^8363 ≤ (16861782981741/100000000000000 : ℝ)^6315 := by
    have hnat : (521501667 : ℕ)^8363*100000000000000^6315 ≤ 16861782981741^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521501667 2000000000 16861782981741 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196000839/2500000000 : ℝ)^8363 ≤ (37665656727367/100000000000000 : ℝ)^6315 := by
    have hnat : (1196000839 : ℕ)^8363*100000000000000^6315 ≤ 37665656727367^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196000839 2500000000 37665656727367 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378804039/2500000000 : ℝ), (-521501667/2000000000 : ℝ), (1196000839/2500000000 : ℝ)] ![(22736280141259/50000000000000 : ℝ), (16861782981741/100000000000000 : ℝ), (37665656727367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378804039/2500000000 : ℝ)|^8363 ≤ (22736280141259/50000000000000 : ℝ)^6315
        have hw : |(1378804039/2500000000 : ℝ)|=(1378804039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-521501667/2000000000 : ℝ)|^8363 ≤ (16861782981741/100000000000000 : ℝ)^6315
        have hw : |(-521501667/2000000000 : ℝ)|=(521501667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1196000839/2500000000 : ℝ)|^8363 ≤ (37665656727367/100000000000000 : ℝ)^6315
        have hw : |(1196000839/2500000000 : ℝ)|=(1196000839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s0_2 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (689402041/1250000000 : ℝ)*x 0 + (2392001597/5000000000 : ℝ)*x 1 + (-325938539/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689402041/1250000000 : ℝ)^8363 ≤ (22736281080277/50000000000000 : ℝ)^6315 := by
    have hnat : (689402041 : ℕ)^8363*50000000000000^6315 ≤ 22736281080277^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689402041 1250000000 22736281080277 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2392001597/5000000000 : ℝ)^8363 ≤ (37665655038257/100000000000000 : ℝ)^6315 := by
    have hnat : (2392001597 : ℕ)^8363*100000000000000^6315 ≤ 37665655038257^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2392001597 5000000000 37665655038257 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325938539/1250000000 : ℝ)^8363 ≤ (16861782784773/100000000000000 : ℝ)^6315 := by
    have hnat : (325938539 : ℕ)^8363*100000000000000^6315 ≤ 16861782784773^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325938539 1250000000 16861782784773 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689402041/1250000000 : ℝ), (2392001597/5000000000 : ℝ), (-325938539/1250000000 : ℝ)] ![(22736281080277/50000000000000 : ℝ), (37665655038257/100000000000000 : ℝ), (16861782784773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689402041/1250000000 : ℝ)|^8363 ≤ (22736281080277/50000000000000 : ℝ)^6315
        have hw : |(689402041/1250000000 : ℝ)|=(689402041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2392001597/5000000000 : ℝ)|^8363 ≤ (37665655038257/100000000000000 : ℝ)^6315
        have hw : |(2392001597/5000000000 : ℝ)|=(2392001597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-325938539/1250000000 : ℝ)|^8363 ≤ (16861782784773/100000000000000 : ℝ)^6315
        have hw : |(-325938539/1250000000 : ℝ)|=(325938539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s0_3 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2099367797/5000000000 : ℝ)*x 0 + (779954157/2500000000 : ℝ)*x 1 + (5648086323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099367797/5000000000 : ℝ)^8363 ≤ (158439387157/500000000000 : ℝ)^6315 := by
    have hnat : (2099367797 : ℕ)^8363*500000000000^6315 ≤ 158439387157^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099367797 5000000000 158439387157 500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779954157/2500000000 : ℝ)^8363 ≤ (21383140055407/100000000000000 : ℝ)^6315 := by
    have hnat : (779954157 : ℕ)^8363*100000000000000^6315 ≤ 21383140055407^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779954157 2500000000 21383140055407 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5648086323/10000000000 : ℝ)^8363 ≤ (23464491247019/50000000000000 : ℝ)^6315 := by
    have hnat : (5648086323 : ℕ)^8363*50000000000000^6315 ≤ 23464491247019^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5648086323 10000000000 23464491247019 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099367797/5000000000 : ℝ), (779954157/2500000000 : ℝ), (5648086323/10000000000 : ℝ)] ![(158439387157/500000000000 : ℝ), (21383140055407/100000000000000 : ℝ), (23464491247019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099367797/5000000000 : ℝ)|^8363 ≤ (158439387157/500000000000 : ℝ)^6315
        have hw : |(2099367797/5000000000 : ℝ)|=(2099367797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779954157/2500000000 : ℝ)|^8363 ≤ (21383140055407/100000000000000 : ℝ)^6315
        have hw : |(779954157/2500000000 : ℝ)|=(779954157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5648086323/10000000000 : ℝ)|^8363 ≤ (23464491247019/50000000000000 : ℝ)^6315
        have hw : |(5648086323/10000000000 : ℝ)|=(5648086323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s0_4 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-472011017/2500000000 : ℝ)*x 0 + (963318641/2000000000 : ℝ)*x 1 + (240565739/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (472011017/2500000000 : ℝ)^8363 ≤ (1099556735129/10000000000000 : ℝ)^6315 := by
    have hnat : (472011017 : ℕ)^8363*10000000000000^6315 ≤ 1099556735129^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472011017 2500000000 1099556735129 10000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (963318641/2000000000 : ℝ)^8363 ≤ (9501458226077/25000000000000 : ℝ)^6315 := by
    have hnat : (963318641 : ℕ)^8363*25000000000000^6315 ≤ 9501458226077^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963318641 2000000000 9501458226077 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240565739/400000000 : ℝ)^8363 ≤ (10199719945123/20000000000000 : ℝ)^6315 := by
    have hnat : (240565739 : ℕ)^8363*20000000000000^6315 ≤ 10199719945123^6315*400000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240565739 400000000 10199719945123 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-472011017/2500000000 : ℝ), (963318641/2000000000 : ℝ), (240565739/400000000 : ℝ)] ![(1099556735129/10000000000000 : ℝ), (9501458226077/25000000000000 : ℝ), (10199719945123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-472011017/2500000000 : ℝ)|^8363 ≤ (1099556735129/10000000000000 : ℝ)^6315
        have hw : |(-472011017/2500000000 : ℝ)|=(472011017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(963318641/2000000000 : ℝ)|^8363 ≤ (9501458226077/25000000000000 : ℝ)^6315
        have hw : |(963318641/2000000000 : ℝ)|=(963318641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(240565739/400000000 : ℝ)|^8363 ≤ (10199719945123/20000000000000 : ℝ)^6315
        have hw : |(240565739/400000000 : ℝ)|=(240565739/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s0_5 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171657871/10000000000 : ℝ)*x 0 + (-1377368389/10000000000 : ℝ)*x 1 + (6014143241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171657871/10000000000 : ℝ)^8363 ≤ (41759747404223/100000000000000 : ℝ)^6315 := by
    have hnat : (5171657871 : ℕ)^8363*100000000000000^6315 ≤ 41759747404223^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171657871 10000000000 41759747404223 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1377368389/10000000000 : ℝ)^8363 ≤ (7241655480773/100000000000000 : ℝ)^6315 := by
    have hnat : (1377368389 : ℕ)^8363*100000000000000^6315 ≤ 7241655480773^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377368389 10000000000 7241655480773 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6014143241/10000000000 : ℝ)^8363 ≤ (25499298548917/50000000000000 : ℝ)^6315 := by
    have hnat : (6014143241 : ℕ)^8363*50000000000000^6315 ≤ 25499298548917^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6014143241 10000000000 25499298548917 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171657871/10000000000 : ℝ), (-1377368389/10000000000 : ℝ), (6014143241/10000000000 : ℝ)] ![(41759747404223/100000000000000 : ℝ), (7241655480773/100000000000000 : ℝ), (25499298548917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171657871/10000000000 : ℝ)|^8363 ≤ (41759747404223/100000000000000 : ℝ)^6315
        have hw : |(5171657871/10000000000 : ℝ)|=(5171657871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1377368389/10000000000 : ℝ)|^8363 ≤ (7241655480773/100000000000000 : ℝ)^6315
        have hw : |(-1377368389/10000000000 : ℝ)|=(1377368389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6014143241/10000000000 : ℝ)|^8363 ≤ (25499298548917/50000000000000 : ℝ)^6315
        have hw : |(6014143241/10000000000 : ℝ)|=(6014143241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s0_6 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (646457229/1250000000 : ℝ)*x 0 + (3007071673/5000000000 : ℝ)*x 1 + (-34434207/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646457229/1250000000 : ℝ)^8363 ≤ (41759746987179/100000000000000 : ℝ)^6315 := by
    have hnat : (646457229 : ℕ)^8363*100000000000000^6315 ≤ 41759746987179^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646457229 1250000000 41759746987179 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3007071673/5000000000 : ℝ)^8363 ≤ (50998598276967/100000000000000 : ℝ)^6315 := by
    have hnat : (3007071673 : ℕ)^8363*100000000000000^6315 ≤ 50998598276967^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3007071673 5000000000 50998598276967 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34434207/250000000 : ℝ)^8363 ≤ (7241654721841/100000000000000 : ℝ)^6315 := by
    have hnat : (34434207 : ℕ)^8363*100000000000000^6315 ≤ 7241654721841^6315*250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34434207 250000000 7241654721841 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646457229/1250000000 : ℝ), (3007071673/5000000000 : ℝ), (-34434207/250000000 : ℝ)] ![(41759746987179/100000000000000 : ℝ), (50998598276967/100000000000000 : ℝ), (7241654721841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646457229/1250000000 : ℝ)|^8363 ≤ (41759746987179/100000000000000 : ℝ)^6315
        have hw : |(646457229/1250000000 : ℝ)|=(646457229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3007071673/5000000000 : ℝ)|^8363 ≤ (50998598276967/100000000000000 : ℝ)^6315
        have hw : |(3007071673/5000000000 : ℝ)|=(3007071673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34434207/250000000 : ℝ)|^8363 ≤ (7241654721841/100000000000000 : ℝ)^6315
        have hw : |(-34434207/250000000 : ℝ)|=(34434207/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s0_7 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1052216329/2500000000 : ℝ)*x 0 + (5582892757/10000000000 : ℝ)*x 1 + (1593653117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052216329/2500000000 : ℝ)^8363 ≤ (15894579528659/50000000000000 : ℝ)^6315 := by
    have hnat : (1052216329 : ℕ)^8363*50000000000000^6315 ≤ 15894579528659^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052216329 2500000000 15894579528659 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5582892757/10000000000 : ℝ)^8363 ≤ (23106487519011/50000000000000 : ℝ)^6315 := by
    have hnat : (5582892757 : ℕ)^8363*50000000000000^6315 ≤ 23106487519011^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5582892757 10000000000 23106487519011 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1593653117/5000000000 : ℝ)^8363 ≤ (21997865893037/100000000000000 : ℝ)^6315 := by
    have hnat : (1593653117 : ℕ)^8363*100000000000000^6315 ≤ 21997865893037^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593653117 5000000000 21997865893037 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052216329/2500000000 : ℝ), (5582892757/10000000000 : ℝ), (1593653117/5000000000 : ℝ)] ![(15894579528659/50000000000000 : ℝ), (23106487519011/50000000000000 : ℝ), (21997865893037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052216329/2500000000 : ℝ)|^8363 ≤ (15894579528659/50000000000000 : ℝ)^6315
        have hw : |(1052216329/2500000000 : ℝ)|=(1052216329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5582892757/10000000000 : ℝ)|^8363 ≤ (23106487519011/50000000000000 : ℝ)^6315
        have hw : |(5582892757/10000000000 : ℝ)|=(5582892757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1593653117/5000000000 : ℝ)|^8363 ≤ (21997865893037/100000000000000 : ℝ)^6315
        have hw : |(1593653117/5000000000 : ℝ)|=(1593653117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1170_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (33/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6927/25000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4181/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4181 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4181*1^1024 ≤ 0^1024*1^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4181/1024 : ℝ) ≤ (2372508820313329691/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4181 ≤ (2372508820313329691/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4181*100000000000000000000^1024 ≤ 2372508820313329691^1024*5^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2372508820313329691 100000000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2372508820313329691/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4181 := by
      have hnat : (1 : ℕ)^1024*1^4181 ≤ 1^4181*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102372508820313329691/100000000000000000000 : ℝ) ≤ (10057593522181959/10000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (102372508820313329691/100000000000000000000 : ℝ)^1024 ≤ (10057593522181959/10000000000000000 : ℝ)^4181 := by
      have hnat : (102372508820313329691 : ℕ)^1024*10000000000000000^4181 ≤ 10057593522181959^4181*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102372508820313329691 100000000000000000000 10057593522181959 10000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10057593522181959/10000000000000000 : ℝ)) (X := (102372508820313329691/100000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52372508820313329691/50000000000000000000 : ℝ) ≤ (5057593522181959/5000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (52372508820313329691/50000000000000000000 : ℝ)^1024 ≤ (5057593522181959/5000000000000000 : ℝ)^4181 := by
      have hnat : (52372508820313329691 : ℕ)^1024*5000000000000000^4181 ≤ 5057593522181959^4181*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52372508820313329691 50000000000000000000 5057593522181959 5000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5057593522181959/5000000000000000 : ℝ)) (X := (52372508820313329691/50000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(57593522181959/4000000000000000 : ℝ)*(0 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(57593522181959/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2372508820313329691/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(57593522181959/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4181/1024 : ℝ) := by
    rw [show (1 : ℝ)+(57593522181959/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10057593522181959/10000000000000000 : ℝ) by norm_num, show 1+(2372508820313329691/100000000000000000000 : ℝ)+(0 : ℝ)=(102372508820313329691/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2372508820313329691/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(57593522181959/4000000000000000 : ℝ)*(2/5 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(57593522181959/4000000000000000 : ℝ)*(2/5 : ℝ)=(5057593522181959/5000000000000000 : ℝ) by norm_num, show 1+2*(2372508820313329691/100000000000000000000 : ℝ)=(52372508820313329691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(57593522181959/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57593522181959/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(57593522181959/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57593522181959/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(57593522181959/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57593522181959/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-9414901/50000000 : ℝ)*X 0 0+(3023940643/5000000000 : ℝ)*X 0 1+(1196000841/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1378804039/2500000000 : ℝ)*X 1 0+(-521501667/2000000000 : ℝ)*X 1 1+(1196000839/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((689402041/1250000000 : ℝ)*X 2 0+(2392001597/5000000000 : ℝ)*X 2 1+(-325938539/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2099367797/5000000000 : ℝ)*X 0 0+(779954157/2500000000 : ℝ)*X 0 1+(5648086323/10000000000 : ℝ)*X 0 2+(2099367797/5000000000 : ℝ)*X 1 0+(779954157/2500000000 : ℝ)*X 1 1+(5648086323/10000000000 : ℝ)*X 1 2+(2099367797/5000000000 : ℝ)*X 2 0+(779954157/2500000000 : ℝ)*X 2 1+(5648086323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-472011017/2500000000 : ℝ)*X 0 0+(963318641/2000000000 : ℝ)*X 0 1+(240565739/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5171657871/10000000000 : ℝ)*X 1 0+(-1377368389/10000000000 : ℝ)*X 1 1+(6014143241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((646457229/1250000000 : ℝ)*X 2 0+(3007071673/5000000000 : ℝ)*X 2 1+(-34434207/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1052216329/2500000000 : ℝ)*X 0 0+(5582892757/10000000000 : ℝ)*X 0 1+(1593653117/5000000000 : ℝ)*X 0 2+(1052216329/2500000000 : ℝ)*X 1 0+(5582892757/10000000000 : ℝ)*X 1 1+(1593653117/5000000000 : ℝ)*X 1 2+(1052216329/2500000000 : ℝ)*X 2 0+(5582892757/10000000000 : ℝ)*X 2 1+(1593653117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (595462127656342521587559/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77400099/100000000000000 : ℝ)*(base1) + (351864677/25000000000000 : ℝ)*(base19) + (667536693/50000000000000 : ℝ)*(base23) + (97060723/100000000000000 : ℝ)*(base24) + (38711379/12500000000000 : ℝ)*(upper3) + (593377511806489/100000000000000 : ℝ)*(major0) + (593377511806489/100000000000000 : ℝ)*(major1) + (593377511806489/100000000000000 : ℝ)*(major2) + (395610159309829/50000000000000 : ℝ)*(sp0) + (395610988968607/50000000000000 : ℝ)*(sp1) + (197805488315453/25000000000000 : ℝ)*(sp2) + (197764445787281/50000000000000 : ℝ)*(sp3) + (3144176363/100000000000000 : ℝ)*(sp4) + (617688753/25000000000000 : ℝ)*(sp7) + (49441429966209/12500000000000 : ℝ)*(f.failure) + (395611692697961/50000000000000 : ℝ)*(f.sum) + (589682412268049/200000000000000000000000000000 : ℝ)*base66 + (2442564394268049/400000000000000000000000000000 : ℝ)*base68 + (5135553453468049/400000000000000000000000000000 : ℝ)*base70 + (2425666146668049/400000000000000000000000000000 : ℝ)*base72 + (704162211068049/200000000000000000000000000000 : ℝ)*base74 + (3631185152268049/400000000000000000000000000000 : ℝ)*base76 + (2503600927468049/400000000000000000000000000000 : ℝ)*base78 + (446121964268049/400000000000000000000000000000 : ℝ)*base80 + (2477180743068049/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (207167/250000000000000000000 : ℝ)*base89 + (207167/250000000000000000000 : ℝ)*base91 + (207167/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (578892925962109761/125000000000000000000000 : ℝ) := by norm_num
    linear_combination (2906159/5000000000000 : ℝ)*(base1) + (231931629/20000000000000 : ℝ)*(base19) + (288581723/25000000000000 : ℝ)*(base23) + (121131611/100000000000000 : ℝ)*(upper3) + (35046973/25000000000000 : ℝ)*(upper5) + (313118135642883/50000000000000 : ℝ)*(major0) + (313118135642883/50000000000000 : ℝ)*(major1) + (313118135642883/50000000000000 : ℝ)*(major2) + (291222479/12500000000000 : ℝ)*(sp1) + (2344317477/100000000000000 : ℝ)*(sp2) + (6680305066559/800000000000 : ℝ)*(sp4) + (417517292879359/50000000000000 : ℝ)*(sp5) + (417517288276163/50000000000000 : ℝ)*(sp6) + (208717127440103/50000000000000 : ℝ)*(sp7) + (208717156501693/50000000000000 : ℝ)*(f.failure) + (167007615039339/20000000000000 : ℝ)*(f.sum) + (66239009747797/100000000000000000000000000000 : ℝ)*base65 + (1229743905947797/200000000000000000000000000000 : ℝ)*base67 + (736166596452203/200000000000000000000000000000 : ℝ)*base70 + (88806683852203/200000000000000000000000000000 : ℝ)*base72 + (471967077347797/100000000000000000000000000000 : ℝ)*base73 + (221481717452203/200000000000000000000000000000 : ℝ)*base76 + (20995987452203/200000000000000000000000000000 : ℝ)*base78 + (682684914147797/200000000000000000000000000000 : ℝ)*base79 + (237954240652203/100000000000000000000000000000 : ℝ)*base82 + (3621341/1000000000000000000000 : ℝ)*base90 + (3621341/1000000000000000000000 : ℝ)*base92 + (3621341/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1170_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (33/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6927/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1170_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1170_s1_0 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-521404731/2500000000 : ℝ)*x 0 + (5694089319/10000000000 : ℝ)*x 1 + (1252018823/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521404731/2500000000 : ℝ)^8363 ≤ (627231636473/5000000000000 : ℝ)^6315 := by
    have hnat : (521404731 : ℕ)^8363*5000000000000^6315 ≤ 627231636473^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521404731 2500000000 627231636473 5000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5694089319/10000000000 : ℝ)^8363 ≤ (11858960275743/25000000000000 : ℝ)^6315 := by
    have hnat : (5694089319 : ℕ)^8363*25000000000000^6315 ≤ 11858960275743^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5694089319 10000000000 11858960275743 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252018823/2500000000 : ℝ)^8363 ≤ (40019526150299/100000000000000 : ℝ)^6315 := by
    have hnat : (1252018823 : ℕ)^8363*100000000000000^6315 ≤ 40019526150299^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252018823 2500000000 40019526150299 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-521404731/2500000000 : ℝ), (5694089319/10000000000 : ℝ), (1252018823/2500000000 : ℝ)] ![(627231636473/5000000000000 : ℝ), (11858960275743/25000000000000 : ℝ), (40019526150299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-521404731/2500000000 : ℝ)|^8363 ≤ (627231636473/5000000000000 : ℝ)^6315
        have hw : |(-521404731/2500000000 : ℝ)|=(521404731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5694089319/10000000000 : ℝ)|^8363 ≤ (11858960275743/25000000000000 : ℝ)^6315
        have hw : |(5694089319/10000000000 : ℝ)|=(5694089319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1252018823/2500000000 : ℝ)|^8363 ≤ (40019526150299/100000000000000 : ℝ)^6315
        have hw : |(1252018823/2500000000 : ℝ)|=(1252018823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s1_1 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1354396517/2500000000 : ℝ)*x 0 + (-2455306093/10000000000 : ℝ)*x 1 + (5008074331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354396517/2500000000 : ℝ)^8363 ≤ (22204813674759/50000000000000 : ℝ)^6315 := by
    have hnat : (1354396517 : ℕ)^8363*50000000000000^6315 ≤ 22204813674759^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354396517 2500000000 22204813674759 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2455306093/10000000000 : ℝ)^8363 ≤ (15570856661047/100000000000000 : ℝ)^6315 := by
    have hnat : (2455306093 : ℕ)^8363*100000000000000^6315 ≤ 15570856661047^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2455306093 10000000000 15570856661047 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5008074331/10000000000 : ℝ)^8363 ≤ (125060987439/312500000000 : ℝ)^6315 := by
    have hnat : (5008074331 : ℕ)^8363*312500000000^6315 ≤ 125060987439^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5008074331 10000000000 125060987439 312500000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354396517/2500000000 : ℝ), (-2455306093/10000000000 : ℝ), (5008074331/10000000000 : ℝ)] ![(22204813674759/50000000000000 : ℝ), (15570856661047/100000000000000 : ℝ), (125060987439/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354396517/2500000000 : ℝ)|^8363 ≤ (22204813674759/50000000000000 : ℝ)^6315
        have hw : |(1354396517/2500000000 : ℝ)|=(1354396517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2455306093/10000000000 : ℝ)|^8363 ≤ (15570856661047/100000000000000 : ℝ)^6315
        have hw : |(-2455306093/10000000000 : ℝ)|=(2455306093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5008074331/10000000000 : ℝ)|^8363 ≤ (125060987439/312500000000 : ℝ)^6315
        have hw : |(5008074331/10000000000 : ℝ)|=(5008074331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s1_2 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (677198523/1250000000 : ℝ)*x 0 + (1252018091/2500000000 : ℝ)*x 1 + (-491061167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677198523/1250000000 : ℝ)^8363 ≤ (22204825160149/50000000000000 : ℝ)^6315 := by
    have hnat : (677198523 : ℕ)^8363*50000000000000^6315 ≤ 22204825160149^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677198523 1250000000 22204825160149 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252018091/2500000000 : ℝ)^8363 ≤ (40019495164631/100000000000000 : ℝ)^6315 := by
    have hnat : (1252018091 : ℕ)^8363*100000000000000^6315 ≤ 40019495164631^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252018091 2500000000 40019495164631 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491061167/2000000000 : ℝ)^8363 ≤ (1946356811783/12500000000000 : ℝ)^6315 := by
    have hnat : (491061167 : ℕ)^8363*12500000000000^6315 ≤ 1946356811783^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491061167 2000000000 1946356811783 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677198523/1250000000 : ℝ), (1252018091/2500000000 : ℝ), (-491061167/2000000000 : ℝ)] ![(22204825160149/50000000000000 : ℝ), (40019495164631/100000000000000 : ℝ), (1946356811783/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677198523/1250000000 : ℝ)|^8363 ≤ (22204825160149/50000000000000 : ℝ)^6315
        have hw : |(677198523/1250000000 : ℝ)|=(677198523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1252018091/2500000000 : ℝ)|^8363 ≤ (40019495164631/100000000000000 : ℝ)^6315
        have hw : |(1252018091/2500000000 : ℝ)|=(1252018091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-491061167/2000000000 : ℝ)|^8363 ≤ (1946356811783/12500000000000 : ℝ)^6315
        have hw : |(-491061167/2000000000 : ℝ)|=(491061167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s1_3 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (863011849/2000000000 : ℝ)*x 0 + (147290827/400000000 : ℝ)*x 1 + (2527286131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863011849/2000000000 : ℝ)^8363 ≤ (32855670929803/100000000000000 : ℝ)^6315 := by
    have hnat : (863011849 : ℕ)^8363*100000000000000^6315 ≤ 32855670929803^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863011849 2000000000 32855670929803 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147290827/400000000 : ℝ)^8363 ≤ (5326401539349/20000000000000 : ℝ)^6315 := by
    have hnat : (147290827 : ℕ)^8363*20000000000000^6315 ≤ 5326401539349^6315*400000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147290827 400000000 5326401539349 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2527286131/5000000000 : ℝ)^8363 ≤ (1620492853853/4000000000000 : ℝ)^6315 := by
    have hnat : (2527286131 : ℕ)^8363*4000000000000^6315 ≤ 1620492853853^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2527286131 5000000000 1620492853853 4000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863011849/2000000000 : ℝ), (147290827/400000000 : ℝ), (2527286131/5000000000 : ℝ)] ![(32855670929803/100000000000000 : ℝ), (5326401539349/20000000000000 : ℝ), (1620492853853/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863011849/2000000000 : ℝ)|^8363 ≤ (32855670929803/100000000000000 : ℝ)^6315
        have hw : |(863011849/2000000000 : ℝ)|=(863011849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(147290827/400000000 : ℝ)|^8363 ≤ (5326401539349/20000000000000 : ℝ)^6315
        have hw : |(147290827/400000000 : ℝ)|=(147290827/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2527286131/5000000000 : ℝ)|^8363 ≤ (1620492853853/4000000000000 : ℝ)^6315
        have hw : |(2527286131/5000000000 : ℝ)|=(2527286131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s1_4 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037491/9765625 : ℝ)*x 0 + (313583901/625000000 : ℝ)*x 1 + (2842318783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037491/9765625 : ℝ)^8363 ≤ (2510156266141/20000000000000 : ℝ)^6315 := by
    have hnat : (2037491 : ℕ)^8363*20000000000000^6315 ≤ 2510156266141^6315*9765625^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037491 9765625 2510156266141 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (313583901/625000000 : ℝ)^8363 ≤ (8023525051147/20000000000000 : ℝ)^6315 := by
    have hnat : (313583901 : ℕ)^8363*20000000000000^6315 ≤ 8023525051147^6315*625000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313583901 625000000 8023525051147 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2842318783/5000000000 : ℝ)^8363 ≤ (591644917541/1250000000000 : ℝ)^6315 := by
    have hnat : (2842318783 : ℕ)^8363*1250000000000^6315 ≤ 591644917541^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842318783 5000000000 591644917541 1250000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037491/9765625 : ℝ), (313583901/625000000 : ℝ), (2842318783/5000000000 : ℝ)] ![(2510156266141/20000000000000 : ℝ), (8023525051147/20000000000000 : ℝ), (591644917541/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037491/9765625 : ℝ)|^8363 ≤ (2510156266141/20000000000000 : ℝ)^6315
        have hw : |(-2037491/9765625 : ℝ)|=(2037491/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(313583901/625000000 : ℝ)|^8363 ≤ (8023525051147/20000000000000 : ℝ)^6315
        have hw : |(313583901/625000000 : ℝ)|=(313583901/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2842318783/5000000000 : ℝ)|^8363 ≤ (591644917541/1250000000000 : ℝ)^6315
        have hw : |(2842318783/5000000000 : ℝ)|=(2842318783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s1_5 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1048291913/2000000000 : ℝ)*x 0 + (-889369927/5000000000 : ℝ)*x 1 + (2842320209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048291913/2000000000 : ℝ)^8363 ≤ (42507795228907/100000000000000 : ℝ)^6315 := by
    have hnat : (1048291913 : ℕ)^8363*100000000000000^6315 ≤ 42507795228907^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048291913 2000000000 42507795228907 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (889369927/5000000000 : ℝ)^8363 ≤ (2032115982157/20000000000000 : ℝ)^6315 := by
    have hnat : (889369927 : ℕ)^8363*20000000000000^6315 ≤ 2032115982157^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889369927 5000000000 2032115982157 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2842320209/5000000000 : ℝ)^8363 ≤ (47331624850817/100000000000000 : ℝ)^6315 := by
    have hnat : (2842320209 : ℕ)^8363*100000000000000^6315 ≤ 47331624850817^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842320209 5000000000 47331624850817 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048291913/2000000000 : ℝ), (-889369927/5000000000 : ℝ), (2842320209/5000000000 : ℝ)] ![(42507795228907/100000000000000 : ℝ), (2032115982157/20000000000000 : ℝ), (47331624850817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048291913/2000000000 : ℝ)|^8363 ≤ (42507795228907/100000000000000 : ℝ)^6315
        have hw : |(1048291913/2000000000 : ℝ)|=(1048291913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-889369927/5000000000 : ℝ)|^8363 ≤ (2032115982157/20000000000000 : ℝ)^6315
        have hw : |(-889369927/5000000000 : ℝ)|=(889369927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2842320209/5000000000 : ℝ)|^8363 ≤ (47331624850817/100000000000000 : ℝ)^6315
        have hw : |(2842320209/5000000000 : ℝ)|=(2842320209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s1_6 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (262072943/500000000 : ℝ)*x 0 + (5684641663/10000000000 : ℝ)*x 1 + (-11117119/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262072943/500000000 : ℝ)^8363 ≤ (42507787657193/100000000000000 : ℝ)^6315 := by
    have hnat : (262072943 : ℕ)^8363*100000000000000^6315 ≤ 42507787657193^6315*500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262072943 500000000 42507787657193 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5684641663/10000000000 : ℝ)^8363 ≤ (47331638578793/100000000000000 : ℝ)^6315 := by
    have hnat : (5684641663 : ℕ)^8363*100000000000000^6315 ≤ 47331638578793^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5684641663 10000000000 47331638578793 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11117119/62500000 : ℝ)^8363 ≤ (2540143438269/25000000000000 : ℝ)^6315 := by
    have hnat : (11117119 : ℕ)^8363*25000000000000^6315 ≤ 2540143438269^6315*62500000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11117119 62500000 2540143438269 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262072943/500000000 : ℝ), (5684641663/10000000000 : ℝ), (-11117119/62500000 : ℝ)] ![(42507787657193/100000000000000 : ℝ), (47331638578793/100000000000000 : ℝ), (2540143438269/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262072943/500000000 : ℝ)|^8363 ≤ (42507787657193/100000000000000 : ℝ)^6315
        have hw : |(262072943/500000000 : ℝ)|=(262072943/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5684641663/10000000000 : ℝ)|^8363 ≤ (47331638578793/100000000000000 : ℝ)^6315
        have hw : |(5684641663/10000000000 : ℝ)|=(5684641663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11117119/62500000 : ℝ)|^8363 ≤ (2540143438269/25000000000000 : ℝ)^6315
        have hw : |(-11117119/62500000 : ℝ)|=(11117119/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s1_7 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4316591607/10000000000 : ℝ)*x 0 + (629504651/1250000000 : ℝ)*x 1 + (3701169793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316591607/10000000000 : ℝ)^8363 ≤ (32871123427889/100000000000000 : ℝ)^6315 := by
    have hnat : (4316591607 : ℕ)^8363*100000000000000^6315 ≤ 32871123427889^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316591607 10000000000 32871123427889 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (629504651/1250000000 : ℝ)^8363 ≤ (20157850877751/50000000000000 : ℝ)^6315 := by
    have hnat : (629504651 : ℕ)^8363*50000000000000^6315 ≤ 20157850877751^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629504651 1250000000 20157850877751 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3701169793/10000000000 : ℝ)^8363 ≤ (26813174804223/100000000000000 : ℝ)^6315 := by
    have hnat : (3701169793 : ℕ)^8363*100000000000000^6315 ≤ 26813174804223^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3701169793 10000000000 26813174804223 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316591607/10000000000 : ℝ), (629504651/1250000000 : ℝ), (3701169793/10000000000 : ℝ)] ![(32871123427889/100000000000000 : ℝ), (20157850877751/50000000000000 : ℝ), (26813174804223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316591607/10000000000 : ℝ)|^8363 ≤ (32871123427889/100000000000000 : ℝ)^6315
        have hw : |(4316591607/10000000000 : ℝ)|=(4316591607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(629504651/1250000000 : ℝ)|^8363 ≤ (20157850877751/50000000000000 : ℝ)^6315
        have hw : |(629504651/1250000000 : ℝ)|=(629504651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3701169793/10000000000 : ℝ)|^8363 ≤ (26813174804223/100000000000000 : ℝ)^6315
        have hw : |(3701169793/10000000000 : ℝ)|=(3701169793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s1_8 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1326117/2500000000 : ℝ)*x 0 + (5490571653/10000000000 : ℝ)*x 1 + (1269786367/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326117/2500000000 : ℝ)^8363 ≤ (1149104671/25000000000000 : ℝ)^6315 := by
    have hnat : (1326117 : ℕ)^8363*25000000000000^6315 ≤ 1149104671^6315*2500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326117 2500000000 1149104671 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490571653/10000000000 : ℝ)^8363 ≤ (11300916655371/25000000000000 : ℝ)^6315 := by
    have hnat : (5490571653 : ℕ)^8363*25000000000000^6315 ≤ 11300916655371^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490571653 10000000000 11300916655371 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1269786367/2000000000 : ℝ)^8363 ≤ (1095834739003/2000000000000 : ℝ)^6315 := by
    have hnat : (1269786367 : ℕ)^8363*2000000000000^6315 ≤ 1095834739003^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269786367 2000000000 1095834739003 2000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326117/2500000000 : ℝ), (5490571653/10000000000 : ℝ), (1269786367/2000000000 : ℝ)] ![(1149104671/25000000000000 : ℝ), (11300916655371/25000000000000 : ℝ), (1095834739003/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326117/2500000000 : ℝ)|^8363 ≤ (1149104671/25000000000000 : ℝ)^6315
        have hw : |(1326117/2500000000 : ℝ)|=(1326117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490571653/10000000000 : ℝ)|^8363 ≤ (11300916655371/25000000000000 : ℝ)^6315
        have hw : |(5490571653/10000000000 : ℝ)|=(5490571653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1269786367/2000000000 : ℝ)|^8363 ≤ (1095834739003/2000000000000 : ℝ)^6315
        have hw : |(1269786367/2000000000 : ℝ)|=(1269786367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s1_9 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (492819317/5000000000 : ℝ)*x 0 + (-2195695693/5000000000 : ℝ)*x 1 + (86831163/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (492819317/5000000000 : ℝ)^8363 ≤ (232457267357/5000000000000 : ℝ)^6315 := by
    have hnat : (492819317 : ℕ)^8363*5000000000000^6315 ≤ 232457267357^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492819317 5000000000 232457267357 5000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195695693/5000000000 : ℝ)^8363 ≤ (33627566980299/100000000000000 : ℝ)^6315 := by
    have hnat : (2195695693 : ℕ)^8363*100000000000000^6315 ≤ 33627566980299^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195695693 5000000000 33627566980299 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86831163/125000000 : ℝ)^8363 ≤ (30861643830621/50000000000000 : ℝ)^6315 := by
    have hnat : (86831163 : ℕ)^8363*50000000000000^6315 ≤ 30861643830621^6315*125000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86831163 125000000 30861643830621 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(492819317/5000000000 : ℝ), (-2195695693/5000000000 : ℝ), (86831163/125000000 : ℝ)] ![(232457267357/5000000000000 : ℝ), (33627566980299/100000000000000 : ℝ), (30861643830621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(492819317/5000000000 : ℝ)|^8363 ≤ (232457267357/5000000000000 : ℝ)^6315
        have hw : |(492819317/5000000000 : ℝ)|=(492819317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2195695693/5000000000 : ℝ)|^8363 ≤ (33627566980299/100000000000000 : ℝ)^6315
        have hw : |(-2195695693/5000000000 : ℝ)|=(2195695693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(86831163/125000000 : ℝ)|^8363 ≤ (30861643830621/50000000000000 : ℝ)^6315
        have hw : |(86831163/125000000 : ℝ)|=(86831163/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s1_10 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (123204043/1250000000 : ℝ)*x 0 + (1389295513/2000000000 : ℝ)*x 1 + (-4391413217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123204043/1250000000 : ℝ)^8363 ≤ (2324553028013/50000000000000 : ℝ)^6315 := by
    have hnat : (123204043 : ℕ)^8363*50000000000000^6315 ≤ 2324553028013^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123204043 1250000000 2324553028013 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1389295513/2000000000 : ℝ)^8363 ≤ (12344621112857/20000000000000 : ℝ)^6315 := by
    have hnat : (1389295513 : ℕ)^8363*20000000000000^6315 ≤ 12344621112857^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389295513 2000000000 12344621112857 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4391413217/10000000000 : ℝ)^8363 ≤ (33627788369291/100000000000000 : ℝ)^6315 := by
    have hnat : (4391413217 : ℕ)^8363*100000000000000^6315 ≤ 33627788369291^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4391413217 10000000000 33627788369291 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(123204043/1250000000 : ℝ), (1389295513/2000000000 : ℝ), (-4391413217/10000000000 : ℝ)] ![(2324553028013/50000000000000 : ℝ), (12344621112857/20000000000000 : ℝ), (33627788369291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(123204043/1250000000 : ℝ)|^8363 ≤ (2324553028013/50000000000000 : ℝ)^6315
        have hw : |(123204043/1250000000 : ℝ)|=(123204043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1389295513/2000000000 : ℝ)|^8363 ≤ (12344621112857/20000000000000 : ℝ)^6315
        have hw : |(1389295513/2000000000 : ℝ)|=(1389295513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4391413217/10000000000 : ℝ)|^8363 ≤ (33627788369291/100000000000000 : ℝ)^6315
        have hw : |(-4391413217/10000000000 : ℝ)|=(4391413217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s1_11 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (956321949/5000000000 : ℝ)*x 0 + (58051593/100000000 : ℝ)*x 1 + (5020327369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (956321949/5000000000 : ℝ)^8363 ≤ (5592846405291/50000000000000 : ℝ)^6315 := by
    have hnat : (956321949 : ℕ)^8363*50000000000000^6315 ≤ 5592846405291^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956321949 5000000000 5592846405291 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58051593/100000000 : ℝ)^8363 ≤ (6083133943223/12500000000000 : ℝ)^6315 := by
    have hnat : (58051593 : ℕ)^8363*12500000000000^6315 ≤ 6083133943223^6315*100000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58051593 100000000 6083133943223 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5020327369/10000000000 : ℝ)^8363 ≤ (10037308906881/25000000000000 : ℝ)^6315 := by
    have hnat : (5020327369 : ℕ)^8363*25000000000000^6315 ≤ 10037308906881^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020327369 10000000000 10037308906881 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(956321949/5000000000 : ℝ), (58051593/100000000 : ℝ), (5020327369/10000000000 : ℝ)] ![(5592846405291/50000000000000 : ℝ), (6083133943223/12500000000000 : ℝ), (10037308906881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(956321949/5000000000 : ℝ)|^8363 ≤ (5592846405291/50000000000000 : ℝ)^6315
        have hw : |(956321949/5000000000 : ℝ)|=(956321949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(58051593/100000000 : ℝ)|^8363 ≤ (6083133943223/12500000000000 : ℝ)^6315
        have hw : |(58051593/100000000 : ℝ)|=(58051593/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5020327369/10000000000 : ℝ)|^8363 ≤ (10037308906881/25000000000000 : ℝ)^6315
        have hw : |(5020327369/10000000000 : ℝ)|=(5020327369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1170_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6927/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (33/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (1161/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20311/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6927/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (33/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6927/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (33/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6927/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (33/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6927/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (33/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6927/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (33/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6927/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (33/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (33/6250 : ℝ) ^ (4181/1024 : ℝ) ≤ (50291722877/100000000000000000000 : ℝ) := by
    have hpowers : (33/6250 : ℝ)^4181 ≤ (50291722877/100000000000000000000 : ℝ)^1024 := by
      have hnat : (33 : ℕ)^4181*100000000000000000000^1024 ≤ 50291722877^1024*6250^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33 6250 50291722877 100000000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33/6250 : ℝ)) (X := (50291722877/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6927/25000 : ℝ) ^ (4181/1024 : ℝ) ≤ (529849575913206361/100000000000000000000 : ℝ) := by
    have hpowers : (6927/25000 : ℝ)^4181 ≤ (529849575913206361/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6927 : ℕ)^4181*100000000000000000000^1024 ≤ 529849575913206361^1024*25000^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6927 25000 529849575913206361 100000000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6927/25000 : ℝ)) (X := (529849575913206361/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000050291722877/50000000000000000000 : ℝ) ≤ (2000000000492693/2000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (50000000050291722877/50000000000000000000 : ℝ)^1024 ≤ (2000000000492693/2000000000000000 : ℝ)^4181 := by
      have hnat : (50000000050291722877 : ℕ)^1024*2000000000000000^4181 ≤ 2000000000492693^4181*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000050291722877 50000000000000000000 2000000000492693 2000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000000492693/2000000000000000 : ℝ)) (X := (50000000050291722877/50000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50264924813102464619/50000000000000000000 : ℝ) ≤ (10012951064811311/10000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (50264924813102464619/50000000000000000000 : ℝ)^1024 ≤ (10012951064811311/10000000000000000 : ℝ)^4181 := by
      have hnat : (50264924813102464619 : ℕ)^1024*10000000000000000^4181 ≤ 10012951064811311^4181*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50264924813102464619 50000000000000000000 10012951064811311 10000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012951064811311/10000000000000000 : ℝ)) (X := (50264924813102464619/50000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50529849575913206361/50000000000000000000 : ℝ) ≤ (10025902127159157/10000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (50529849575913206361/50000000000000000000 : ℝ)^1024 ≤ (10025902127159157/10000000000000000 : ℝ)^4181 := by
      have hnat : (50529849575913206361 : ℕ)^1024*10000000000000000^4181 ≤ 10025902127159157^4181*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50529849575913206361 50000000000000000000 10025902127159157 10000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10025902127159157/10000000000000000 : ℝ)) (X := (50529849575913206361/50000000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(50291722877/100000000000000000000 : ℝ) ≤ ((22648860312093137777/22650000000000000000 : ℝ)+2*(6475531173923/1359000000000000 : ℝ)*(33/6250 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (22648860312093137777/22650000000000000000 : ℝ)+2*(6475531173923/1359000000000000 : ℝ)*(33/6250 : ℝ)=(2000000000492693/2000000000000000 : ℝ) by norm_num, show 1+2*(50291722877/100000000000000000000 : ℝ)=(50000000050291722877/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(529849575913206361/100000000000000000000 : ℝ)+(50291722877/100000000000000000000 : ℝ) ≤ ((22648860312093137777/22650000000000000000 : ℝ)+(6475531173923/1359000000000000 : ℝ)*((6927/25000 : ℝ)+(33/6250 : ℝ)))^(4181/1024 : ℝ) := by
    rw [show (22648860312093137777/22650000000000000000 : ℝ)+(6475531173923/1359000000000000 : ℝ)*((6927/25000 : ℝ)+(33/6250 : ℝ))=(10012951064811311/10000000000000000 : ℝ) by norm_num, show 1+(529849575913206361/100000000000000000000 : ℝ)+(50291722877/100000000000000000000 : ℝ)=(50264924813102464619/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(529849575913206361/100000000000000000000 : ℝ) ≤ ((22648860312093137777/22650000000000000000 : ℝ)+2*(6475531173923/1359000000000000 : ℝ)*(6927/25000 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (22648860312093137777/22650000000000000000 : ℝ)+2*(6475531173923/1359000000000000 : ℝ)*(6927/25000 : ℝ)=(10025902127159157/10000000000000000 : ℝ) by norm_num, show 1+2*(529849575913206361/100000000000000000000 : ℝ)=(50529849575913206361/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22648860312093137777/22650000000000000000 : ℝ)*(X 1 0+X 2 0)+(6475531173923/1359000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (33/6250 : ℝ)) (hi := (6927/25000 : ℝ)) (c := (22648860312093137777/22650000000000000000 : ℝ)) (alpha := (6475531173923/1359000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22648860312093137777/22650000000000000000 : ℝ)*(X 0 1+X 2 1)+(6475531173923/1359000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (33/6250 : ℝ)) (hi := (6927/25000 : ℝ)) (c := (22648860312093137777/22650000000000000000 : ℝ)) (alpha := (6475531173923/1359000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22648860312093137777/22650000000000000000 : ℝ)*(X 0 2+X 1 2)+(6475531173923/1359000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (33/6250 : ℝ)) (hi := (6927/25000 : ℝ)) (c := (22648860312093137777/22650000000000000000 : ℝ)) (alpha := (6475531173923/1359000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-521404731/2500000000 : ℝ)*X 0 0+(5694089319/10000000000 : ℝ)*X 0 1+(1252018823/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1354396517/2500000000 : ℝ)*X 1 0+(-2455306093/10000000000 : ℝ)*X 1 1+(5008074331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((677198523/1250000000 : ℝ)*X 2 0+(1252018091/2500000000 : ℝ)*X 2 1+(-491061167/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((863011849/2000000000 : ℝ)*X 0 0+(147290827/400000000 : ℝ)*X 0 1+(2527286131/5000000000 : ℝ)*X 0 2+(863011849/2000000000 : ℝ)*X 1 0+(147290827/400000000 : ℝ)*X 1 1+(2527286131/5000000000 : ℝ)*X 1 2+(863011849/2000000000 : ℝ)*X 2 0+(147290827/400000000 : ℝ)*X 2 1+(2527286131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2037491/9765625 : ℝ)*X 0 0+(313583901/625000000 : ℝ)*X 0 1+(2842318783/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1048291913/2000000000 : ℝ)*X 1 0+(-889369927/5000000000 : ℝ)*X 1 1+(2842320209/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((262072943/500000000 : ℝ)*X 2 0+(5684641663/10000000000 : ℝ)*X 2 1+(-11117119/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4316591607/10000000000 : ℝ)*X 0 0+(629504651/1250000000 : ℝ)*X 0 1+(3701169793/10000000000 : ℝ)*X 0 2+(4316591607/10000000000 : ℝ)*X 1 0+(629504651/1250000000 : ℝ)*X 1 1+(3701169793/10000000000 : ℝ)*X 1 2+(4316591607/10000000000 : ℝ)*X 2 0+(629504651/1250000000 : ℝ)*X 2 1+(3701169793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((1326117/2500000000 : ℝ)*X 0 0+(5490571653/10000000000 : ℝ)*X 0 1+(1269786367/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((492819317/5000000000 : ℝ)*X 1 0+(-2195695693/5000000000 : ℝ)*X 1 1+(86831163/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((123204043/1250000000 : ℝ)*X 2 0+(1389295513/2000000000 : ℝ)*X 2 1+(-4391413217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((956321949/5000000000 : ℝ)*X 0 0+(58051593/100000000 : ℝ)*X 0 1+(5020327369/10000000000 : ℝ)*X 0 2+(956321949/5000000000 : ℝ)*X 1 0+(58051593/100000000 : ℝ)*X 1 1+(5020327369/10000000000 : ℝ)*X 1 2+(956321949/5000000000 : ℝ)*X 2 0+(58051593/100000000 : ℝ)*X 2 1+(5020327369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2119173745354659760382970913/377500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162475493/50000000000000 : ℝ)*(lower2) + (1093202385884677/100000000000000 : ℝ)*(major0) + (1093202385884677/100000000000000 : ℝ)*(major1) + (1093202385884677/100000000000000 : ℝ)*(major2) + (728848756333737/50000000000000 : ℝ)*(sp0) + (728848476397123/50000000000000 : ℝ)*(sp1) + (1457695234117347/100000000000000 : ℝ)*(sp2) + (145740397146407/20000000000000 : ℝ)*(sp3) + (166882053/4000000000000 : ℝ)*(sp4) + (3921969289/100000000000000 : ℝ)*(sp5) + (5750552071/100000000000000 : ℝ)*(sp6) + (12655551/1562500000000 : ℝ)*(sp9) + (350024691/50000000000000 : ℝ)*(sp10) + (457097501/50000000000000 : ℝ)*(sp11) + (364351449963519/50000000000000 : ℝ)*(f.failure) + (1457701684718799/100000000000000 : ℝ)*(f.sum) + (481961282447621/67950000000000000000000000000 : ℝ)*base65 + (42927369568230979087/6795000000000000000000000000000000 : ℝ)*base67 + (45855018183405979087/6795000000000000000000000000000000 : ℝ)*base69 + (71632567596675979087/6795000000000000000000000000000000 : ℝ)*base71 + (225666993943721/67950000000000000000000000000 : ℝ)*base73 + (34425437946555979087/6795000000000000000000000000000000 : ℝ)*base75 + (42877453117710979087/6795000000000000000000000000000000 : ℝ)*base77 + (13010779773255979087/6795000000000000000000000000000000 : ℝ)*base79 + (385511364977321/67950000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1777697/1000000000000000000000 : ℝ)*base89 + (1777697/1000000000000000000000 : ℝ)*base91 + (1777697/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11598224591063053624999/3775000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70241487728189/6250000000000 : ℝ)*(major0) + (70241487728189/6250000000000 : ℝ)*(major1) + (70241487728189/6250000000000 : ℝ)*(major2) + (824737939/20000000000000 : ℝ)*(sp1) + (3275757459/50000000000000 : ℝ)*(sp2) + (653630393/50000000000000 : ℝ)*(sp3) + (749291883967597/50000000000000 : ℝ)*(sp4) + (749291039951787/50000000000000 : ℝ)*(sp5) + (1498579799847963/100000000000000 : ℝ)*(sp6) + (749138841265639/100000000000000 : ℝ)*(sp7) + (83120629/3125000000000 : ℝ)*(sp8) + (224202053/100000000000000 : ℝ)*(sp9) + (1910811/2500000000000 : ℝ)*(sp10) + (232141929/25000000000000 : ℝ)*(sp11) + (374570538547071/50000000000000 : ℝ)*(f.failure) + (749293213897661/50000000000000 : ℝ)*(f.sum) + (74883841958051/33975000000000000000000000000 : ℝ)*base65 + (470325091667812559/424687500000000000000000000000000 : ℝ)*base67 + (724323817370624941/424687500000000000000000000000000 : ℝ)*base70 + (1371960803596874941/424687500000000000000000000000000 : ℝ)*base72 + (172222734940901/33975000000000000000000000000 : ℝ)*base73 + (804042508079062441/424687500000000000000000000000000 : ℝ)*base76 + (112491764990625059/424687500000000000000000000000000 : ℝ)*base77 + (2565700544184375059/424687500000000000000000000000000 : ℝ)*base79 + (983354659901/33975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6749473/1000000000000000000000 : ℝ)*base89 + (6749473/1000000000000000000000 : ℝ)*base91 + (6749473/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1170_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6927/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (33/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1161/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20311/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1170_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1170_s2_0 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-66792607/312500000 : ℝ)*x 0 + (2752776403/5000000000 : ℝ)*x 1 + (1032736239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66792607/312500000 : ℝ)^8363 ≤ (12958451312419/100000000000000 : ℝ)^6315 := by
    have hnat : (66792607 : ℕ)^8363*100000000000000^6315 ≤ 12958451312419^6315*312500000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66792607 312500000 12958451312419 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2752776403/5000000000 : ℝ)^8363 ≤ (45367077915809/100000000000000 : ℝ)^6315 := by
    have hnat : (2752776403 : ℕ)^8363*100000000000000^6315 ≤ 45367077915809^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752776403 5000000000 45367077915809 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032736239/2000000000 : ℝ)^8363 ≤ (4167447076021/10000000000000 : ℝ)^6315 := by
    have hnat : (1032736239 : ℕ)^8363*10000000000000^6315 ≤ 4167447076021^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032736239 2000000000 4167447076021 10000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66792607/312500000 : ℝ), (2752776403/5000000000 : ℝ), (1032736239/2000000000 : ℝ)] ![(12958451312419/100000000000000 : ℝ), (45367077915809/100000000000000 : ℝ), (4167447076021/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66792607/312500000 : ℝ)|^8363 ≤ (12958451312419/100000000000000 : ℝ)^6315
        have hw : |(-66792607/312500000 : ℝ)|=(66792607/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2752776403/5000000000 : ℝ)|^8363 ≤ (45367077915809/100000000000000 : ℝ)^6315
        have hw : |(2752776403/5000000000 : ℝ)|=(2752776403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032736239/2000000000 : ℝ)|^8363 ≤ (4167447076021/10000000000000 : ℝ)^6315
        have hw : |(1032736239/2000000000 : ℝ)|=(1032736239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s2_1 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2686333741/5000000000 : ℝ)*x 0 + (-2314910763/10000000000 : ℝ)*x 1 + (516368403/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686333741/5000000000 : ℝ)^8363 ≤ (8784531796877/20000000000000 : ℝ)^6315 := by
    have hnat : (2686333741 : ℕ)^8363*20000000000000^6315 ≤ 8784531796877^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686333741 5000000000 8784531796877 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2314910763/10000000000 : ℝ)^8363 ≤ (1800354991819/12500000000000 : ℝ)^6315 := by
    have hnat : (2314910763 : ℕ)^8363*12500000000000^6315 ≤ 1800354991819^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2314910763 10000000000 1800354991819 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516368403/1000000000 : ℝ)^8363 ≤ (416745010609/1000000000000 : ℝ)^6315 := by
    have hnat : (516368403 : ℕ)^8363*1000000000000^6315 ≤ 416745010609^6315*1000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516368403 1000000000 416745010609 1000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686333741/5000000000 : ℝ), (-2314910763/10000000000 : ℝ), (516368403/1000000000 : ℝ)] ![(8784531796877/20000000000000 : ℝ), (1800354991819/12500000000000 : ℝ), (416745010609/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686333741/5000000000 : ℝ)|^8363 ≤ (8784531796877/20000000000000 : ℝ)^6315
        have hw : |(2686333741/5000000000 : ℝ)|=(2686333741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2314910763/10000000000 : ℝ)|^8363 ≤ (1800354991819/12500000000000 : ℝ)^6315
        have hw : |(-2314910763/10000000000 : ℝ)|=(2314910763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516368403/1000000000 : ℝ)|^8363 ≤ (416745010609/1000000000000 : ℝ)^6315
        have hw : |(516368403/1000000000 : ℝ)|=(516368403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s2_2 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (671583507/1250000000 : ℝ)*x 0 + (5163683077/10000000000 : ℝ)*x 1 + (-462982249/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671583507/1250000000 : ℝ)^8363 ≤ (21961332599393/50000000000000 : ℝ)^6315 := by
    have hnat : (671583507 : ℕ)^8363*50000000000000^6315 ≤ 21961332599393^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671583507 1250000000 21961332599393 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5163683077/10000000000 : ℝ)^8363 ≤ (10418622718791/25000000000000 : ℝ)^6315 := by
    have hnat : (5163683077 : ℕ)^8363*25000000000000^6315 ≤ 10418622718791^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5163683077 10000000000 10418622718791 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (462982249/2000000000 : ℝ)^8363 ≤ (1800355488251/12500000000000 : ℝ)^6315 := by
    have hnat : (462982249 : ℕ)^8363*12500000000000^6315 ≤ 1800355488251^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462982249 2000000000 1800355488251 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671583507/1250000000 : ℝ), (5163683077/10000000000 : ℝ), (-462982249/2000000000 : ℝ)] ![(21961332599393/50000000000000 : ℝ), (10418622718791/25000000000000 : ℝ), (1800355488251/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671583507/1250000000 : ℝ)|^8363 ≤ (21961332599393/50000000000000 : ℝ)^6315
        have hw : |(671583507/1250000000 : ℝ)|=(671583507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5163683077/10000000000 : ℝ)|^8363 ≤ (10418622718791/25000000000000 : ℝ)^6315
        have hw : |(5163683077/10000000000 : ℝ)|=(5163683077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-462982249/2000000000 : ℝ)|^8363 ≤ (1800355488251/12500000000000 : ℝ)^6315
        have hw : |(-462982249/2000000000 : ℝ)|=(462982249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s2_3 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350625103/10000000000 : ℝ)*x 0 + (2010958733/5000000000 : ℝ)*x 1 + (4705794897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350625103/10000000000 : ℝ)^8363 ≤ (33214778524099/100000000000000 : ℝ)^6315 := by
    have hnat : (4350625103 : ℕ)^8363*100000000000000^6315 ≤ 33214778524099^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350625103 10000000000 33214778524099 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010958733/5000000000 : ℝ)^8363 ≤ (29932843565409/100000000000000 : ℝ)^6315 := by
    have hnat : (2010958733 : ℕ)^8363*100000000000000^6315 ≤ 29932843565409^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010958733 5000000000 29932843565409 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4705794897/10000000000 : ℝ)^8363 ≤ (9213094472529/25000000000000 : ℝ)^6315 := by
    have hnat : (4705794897 : ℕ)^8363*25000000000000^6315 ≤ 9213094472529^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4705794897 10000000000 9213094472529 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350625103/10000000000 : ℝ), (2010958733/5000000000 : ℝ), (4705794897/10000000000 : ℝ)] ![(33214778524099/100000000000000 : ℝ), (29932843565409/100000000000000 : ℝ), (9213094472529/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350625103/10000000000 : ℝ)|^8363 ≤ (33214778524099/100000000000000 : ℝ)^6315
        have hw : |(4350625103/10000000000 : ℝ)|=(4350625103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010958733/5000000000 : ℝ)|^8363 ≤ (29932843565409/100000000000000 : ℝ)^6315
        have hw : |(2010958733/5000000000 : ℝ)|=(2010958733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4705794897/10000000000 : ℝ)|^8363 ≤ (9213094472529/25000000000000 : ℝ)^6315
        have hw : |(4705794897/10000000000 : ℝ)|=(4705794897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s2_4 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-106872893/500000000 : ℝ)*x 0 + (645749173/1250000000 : ℝ)*x 1 + (1100643677/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106872893/500000000 : ℝ)^8363 ≤ (1619901193501/12500000000000 : ℝ)^6315 := by
    have hnat : (106872893 : ℕ)^8363*12500000000000^6315 ≤ 1619901193501^6315*500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106872893 500000000 1619901193501 12500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (645749173/1250000000 : ℝ)^8363 ≤ (66718696639/160000000000 : ℝ)^6315 := by
    have hnat : (645749173 : ℕ)^8363*160000000000^6315 ≤ 66718696639^6315*1250000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645749173 1250000000 66718696639 160000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100643677/2000000000 : ℝ)^8363 ≤ (2833850315161/6250000000000 : ℝ)^6315 := by
    have hnat : (1100643677 : ℕ)^8363*6250000000000^6315 ≤ 2833850315161^6315*2000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100643677 2000000000 2833850315161 6250000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106872893/500000000 : ℝ), (645749173/1250000000 : ℝ), (1100643677/2000000000 : ℝ)] ![(1619901193501/12500000000000 : ℝ), (66718696639/160000000000 : ℝ), (2833850315161/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106872893/500000000 : ℝ)|^8363 ≤ (1619901193501/12500000000000 : ℝ)^6315
        have hw : |(-106872893/500000000 : ℝ)|=(106872893/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(645749173/1250000000 : ℝ)|^8363 ≤ (66718696639/160000000000 : ℝ)^6315
        have hw : |(645749173/1250000000 : ℝ)|=(645749173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100643677/2000000000 : ℝ)|^8363 ≤ (2833850315161/6250000000000 : ℝ)^6315
        have hw : |(1100643677/2000000000 : ℝ)|=(1100643677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s2_5 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5285764991/10000000000 : ℝ)*x 0 + (-1975375219/10000000000 : ℝ)*x 1 + (5503218383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285764991/10000000000 : ℝ)^8363 ≤ (42984287362657/100000000000000 : ℝ)^6315 := by
    have hnat : (5285764991 : ℕ)^8363*100000000000000^6315 ≤ 42984287362657^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285764991 10000000000 42984287362657 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1975375219/10000000000 : ℝ)^8363 ≤ (11674107604887/100000000000000 : ℝ)^6315 := by
    have hnat : (1975375219 : ℕ)^8363*100000000000000^6315 ≤ 11674107604887^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975375219 10000000000 11674107604887 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5503218383/10000000000 : ℝ)^8363 ≤ (22670802510377/50000000000000 : ℝ)^6315 := by
    have hnat : (5503218383 : ℕ)^8363*50000000000000^6315 ≤ 22670802510377^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503218383 10000000000 22670802510377 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285764991/10000000000 : ℝ), (-1975375219/10000000000 : ℝ), (5503218383/10000000000 : ℝ)] ![(42984287362657/100000000000000 : ℝ), (11674107604887/100000000000000 : ℝ), (22670802510377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285764991/10000000000 : ℝ)|^8363 ≤ (42984287362657/100000000000000 : ℝ)^6315
        have hw : |(5285764991/10000000000 : ℝ)|=(5285764991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1975375219/10000000000 : ℝ)|^8363 ≤ (11674107604887/100000000000000 : ℝ)^6315
        have hw : |(-1975375219/10000000000 : ℝ)|=(1975375219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5503218383/10000000000 : ℝ)|^8363 ≤ (22670802510377/50000000000000 : ℝ)^6315
        have hw : |(5503218383/10000000000 : ℝ)|=(5503218383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s2_6 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2642882561/5000000000 : ℝ)*x 0 + (275160919/500000000 : ℝ)*x 1 + (-987687521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642882561/5000000000 : ℝ)^8363 ≤ (21492144386723/50000000000000 : ℝ)^6315 := by
    have hnat : (2642882561 : ℕ)^8363*50000000000000^6315 ≤ 21492144386723^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642882561 5000000000 21492144386723 50000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275160919/500000000 : ℝ)^8363 ≤ (45341604988021/100000000000000 : ℝ)^6315 := by
    have hnat : (275160919 : ℕ)^8363*100000000000000^6315 ≤ 45341604988021^6315*500000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275160919 500000000 45341604988021 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (987687521/5000000000 : ℝ)^8363 ≤ (11674106219611/100000000000000 : ℝ)^6315 := by
    have hnat : (987687521 : ℕ)^8363*100000000000000^6315 ≤ 11674106219611^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987687521 5000000000 11674106219611 100000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642882561/5000000000 : ℝ), (275160919/500000000 : ℝ), (-987687521/5000000000 : ℝ)] ![(21492144386723/50000000000000 : ℝ), (45341604988021/100000000000000 : ℝ), (11674106219611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642882561/5000000000 : ℝ)|^8363 ≤ (21492144386723/50000000000000 : ℝ)^6315
        have hw : |(2642882561/5000000000 : ℝ)|=(2642882561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(275160919/500000000 : ℝ)|^8363 ≤ (45341604988021/100000000000000 : ℝ)^6315
        have hw : |(275160919/500000000 : ℝ)|=(275160919/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-987687521/5000000000 : ℝ)|^8363 ≤ (11674106219611/100000000000000 : ℝ)^6315
        have hw : |(-987687521/5000000000 : ℝ)|=(987687521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1170_s2_7 (p : ℝ) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350815661/10000000000 : ℝ)*x 0 + (2350586027/5000000000 : ℝ)*x 1 + (4026584709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350815661/10000000000 : ℝ)^8363 ≤ (8304176288961/25000000000000 : ℝ)^6315 := by
    have hnat : (4350815661 : ℕ)^8363*25000000000000^6315 ≤ 8304176288961^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350815661 10000000000 8304176288961 25000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2350586027/5000000000 : ℝ)^8363 ≤ (7360888390959/20000000000000 : ℝ)^6315 := by
    have hnat : (2350586027 : ℕ)^8363*20000000000000^6315 ≤ 7360888390959^6315*5000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2350586027 5000000000 7360888390959 20000000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4026584709/10000000000 : ℝ)^8363 ≤ (749471321751/2500000000000 : ℝ)^6315 := by
    have hnat : (4026584709 : ℕ)^8363*2500000000000^6315 ≤ 749471321751^6315*10000000000^8363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026584709 10000000000 749471321751 2500000000000 8363 6315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8363/2048 : ℝ)) 8363 6315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350815661/10000000000 : ℝ), (2350586027/5000000000 : ℝ), (4026584709/10000000000 : ℝ)] ![(8304176288961/25000000000000 : ℝ), (7360888390959/20000000000000 : ℝ), (749471321751/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350815661/10000000000 : ℝ)|^8363 ≤ (8304176288961/25000000000000 : ℝ)^6315
        have hw : |(4350815661/10000000000 : ℝ)|=(4350815661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2350586027/5000000000 : ℝ)|^8363 ≤ (7360888390959/20000000000000 : ℝ)^6315
        have hw : |(2350586027/5000000000 : ℝ)|=(2350586027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4026584709/10000000000 : ℝ)|^8363 ≤ (749471321751/2500000000000 : ℝ)^6315
        have hw : |(4026584709/10000000000 : ℝ)|=(4026584709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1170_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1161/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1839/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (821/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20311/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1161/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20311/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1161/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20311/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1161/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20311/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1161/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20311/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1161/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20311/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1161/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1161/20000 : ℝ) ^ (4181/1024 : ℝ) ≤ (112073990612649/12500000000000000000 : ℝ) := by
    have hpowers : (1161/20000 : ℝ)^4181 ≤ (112073990612649/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1161 : ℕ)^4181*12500000000000000000^1024 ≤ 112073990612649^1024*20000^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1161 20000 112073990612649 12500000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1161/20000 : ℝ)) (X := (112073990612649/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20311/100000 : ℝ) ^ (4181/1024 : ℝ) ≤ (18636807856988453/12500000000000000000 : ℝ) := by
    have hpowers : (20311/100000 : ℝ)^4181 ≤ (18636807856988453/12500000000000000000 : ℝ)^1024 := by
      have hnat : (20311 : ℕ)^4181*12500000000000000000^1024 ≤ 18636807856988453^1024*100000^4181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20311 100000 18636807856988453 12500000000000000000 4181 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20311/100000 : ℝ)) (X := (18636807856988453/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250112073990612649/6250000000000000000 : ℝ) ≤ (2000008783582067/2000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (6250112073990612649/6250000000000000000 : ℝ)^1024 ≤ (2000008783582067/2000000000000000 : ℝ)^4181 := by
      have hnat : (6250112073990612649 : ℕ)^1024*2000000000000000^4181 ≤ 2000008783582067^4181*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250112073990612649 6250000000000000000 2000008783582067 2000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000008783582067/2000000000000000 : ℝ)) (X := (6250112073990612649/6250000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6259374440923800551/6250000000000000000 : ℝ) ≤ (10003671464750181/10000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (6259374440923800551/6250000000000000000 : ℝ)^1024 ≤ (10003671464750181/10000000000000000 : ℝ)^4181 := by
      have hnat : (6259374440923800551 : ℕ)^1024*10000000000000000^4181 ≤ 10003671464750181^4181*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6259374440923800551 6250000000000000000 10003671464750181 10000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003671464750181/10000000000000000 : ℝ)) (X := (6259374440923800551/6250000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6268636807856988453/6250000000000000000 : ℝ) ≤ (10007299011590027/10000000000000000 : ℝ) ^ (4181/1024 : ℝ) := by
    have hpowers : (6268636807856988453/6250000000000000000 : ℝ)^1024 ≤ (10007299011590027/10000000000000000 : ℝ)^4181 := by
      have hnat : (6268636807856988453 : ℕ)^1024*10000000000000000^4181 ≤ 10007299011590027^4181*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6268636807856988453 6250000000000000000 10007299011590027 10000000000000000 1024 4181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007299011590027/10000000000000000 : ℝ)) (X := (6268636807856988453/6250000000000000000 : ℝ)) (by norm_num) 4181 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(112073990612649/12500000000000000000 : ℝ) ≤ ((2900370425087934149/2901200000000000000 : ℝ)+2*(1813773419923/725300000000000 : ℝ)*(1161/20000 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (2900370425087934149/2901200000000000000 : ℝ)+2*(1813773419923/725300000000000 : ℝ)*(1161/20000 : ℝ)=(2000008783582067/2000000000000000 : ℝ) by norm_num, show 1+2*(112073990612649/12500000000000000000 : ℝ)=(6250112073990612649/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18636807856988453/12500000000000000000 : ℝ)+(112073990612649/12500000000000000000 : ℝ) ≤ ((2900370425087934149/2901200000000000000 : ℝ)+(1813773419923/725300000000000 : ℝ)*((20311/100000 : ℝ)+(1161/20000 : ℝ)))^(4181/1024 : ℝ) := by
    rw [show (2900370425087934149/2901200000000000000 : ℝ)+(1813773419923/725300000000000 : ℝ)*((20311/100000 : ℝ)+(1161/20000 : ℝ))=(10003671464750181/10000000000000000 : ℝ) by norm_num, show 1+(18636807856988453/12500000000000000000 : ℝ)+(112073990612649/12500000000000000000 : ℝ)=(6259374440923800551/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18636807856988453/12500000000000000000 : ℝ) ≤ ((2900370425087934149/2901200000000000000 : ℝ)+2*(1813773419923/725300000000000 : ℝ)*(20311/100000 : ℝ))^(4181/1024 : ℝ) := by
    rw [show (2900370425087934149/2901200000000000000 : ℝ)+2*(1813773419923/725300000000000 : ℝ)*(20311/100000 : ℝ)=(10007299011590027/10000000000000000 : ℝ) by norm_num, show 1+2*(18636807856988453/12500000000000000000 : ℝ)=(6268636807856988453/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2900370425087934149/2901200000000000000 : ℝ)*(X 1 0+X 2 0)+(1813773419923/725300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (1161/20000 : ℝ)) (hi := (20311/100000 : ℝ)) (c := (2900370425087934149/2901200000000000000 : ℝ)) (alpha := (1813773419923/725300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2900370425087934149/2901200000000000000 : ℝ)*(X 0 1+X 2 1)+(1813773419923/725300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (1161/20000 : ℝ)) (hi := (20311/100000 : ℝ)) (c := (2900370425087934149/2901200000000000000 : ℝ)) (alpha := (1813773419923/725300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2900370425087934149/2901200000000000000 : ℝ)*(X 0 2+X 1 2)+(1813773419923/725300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4181/1024 : ℝ)) (lo := (1161/20000 : ℝ)) (hi := (20311/100000 : ℝ)) (c := (2900370425087934149/2901200000000000000 : ℝ)) (alpha := (1813773419923/725300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66792607/312500000 : ℝ)*X 0 0+(2752776403/5000000000 : ℝ)*X 0 1+(1032736239/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686333741/5000000000 : ℝ)*X 1 0+(-2314910763/10000000000 : ℝ)*X 1 1+(516368403/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671583507/1250000000 : ℝ)*X 2 0+(5163683077/10000000000 : ℝ)*X 2 1+(-462982249/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350625103/10000000000 : ℝ)*X 0 0+(2010958733/5000000000 : ℝ)*X 0 1+(4705794897/10000000000 : ℝ)*X 0 2+(4350625103/10000000000 : ℝ)*X 1 0+(2010958733/5000000000 : ℝ)*X 1 1+(4705794897/10000000000 : ℝ)*X 1 2+(4350625103/10000000000 : ℝ)*X 2 0+(2010958733/5000000000 : ℝ)*X 2 1+(4705794897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-106872893/500000000 : ℝ)*X 0 0+(645749173/1250000000 : ℝ)*X 0 1+(1100643677/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5285764991/10000000000 : ℝ)*X 1 0+(-1975375219/10000000000 : ℝ)*X 1 1+(5503218383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2642882561/5000000000 : ℝ)*X 2 0+(275160919/500000000 : ℝ)*X 2 1+(-987687521/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350815661/10000000000 : ℝ)*X 0 0+(2350586027/5000000000 : ℝ)*X 0 1+(4026584709/10000000000 : ℝ)*X 0 2+(4350815661/10000000000 : ℝ)*X 1 0+(2350586027/5000000000 : ℝ)*X 1 1+(4026584709/10000000000 : ℝ)*X 1 2+(4350815661/10000000000 : ℝ)*X 2 0+(2350586027/5000000000 : ℝ)*X 2 1+(4026584709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1170_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1267710633966130389230845029/145060000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1027259303/100000000000000 : ℝ)*(base19) + (1047802143/100000000000000 : ℝ)*(base23) + (34185039/100000000000000 : ℝ)*(upper2) + (23416313/5000000000000 : ℝ)*(upper3) + (191050497/100000000000000 : ℝ)*(upper4) + (2193699726725707/100000000000000 : ℝ)*(major0) + (2193699726725707/100000000000000 : ℝ)*(major1) + (2193699726725707/100000000000000 : ℝ)*(major2) + (2925105454828349/100000000000000 : ℝ)*(sp0) + (1462564845145393/50000000000000 : ℝ)*(sp1) + (1462564834873973/50000000000000 : ℝ)*(sp2) + (73112844068733/5000000000000 : ℝ)*(sp3) + (25262721739/100000000000000 : ℝ)*(sp4) + (2312643893/20000000000000 : ℝ)*(sp7) + (731134222297063/50000000000000 : ℝ)*(f.failure) + (365641339693761/12500000000000 : ℝ)*(f.sum) + (10527003332031/9066250000000000000000000000 : ℝ)*base66 + (477220076474912343/290120000000000000000000000000000 : ℝ)*base67 + (790339474380712343/290120000000000000000000000000000 : ℝ)*base69 + (1973869610549927657/290120000000000000000000000000000 : ℝ)*base72 + (114458612856281/36265000000000000000000000000 : ℝ)*base73 + (2353452780000487657/290120000000000000000000000000000 : ℝ)*base76 + (2548130853564807657/290120000000000000000000000000000 : ℝ)*base78 + (2140659689937727657/290120000000000000000000000000000 : ℝ)*base80 + (124633158323893/18132500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (12966969/1000000000000000000000 : ℝ)*base89 + (12966969/1000000000000000000000 : ℝ)*base91 + (12966969/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (210285042008702850467758203/72530000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3130953/390625000000 : ℝ)*(base19) + (485162187/50000000000000 : ℝ)*(base23) + (26535953/100000000000000 : ℝ)*(upper2) + (3275359/3125000000000 : ℝ)*(upper3) + (33054597/50000000000000 : ℝ)*(upper5) + (2223883433249051/100000000000000 : ℝ)*(major0) + (2223883433249051/100000000000000 : ℝ)*(major1) + (2223883433249051/100000000000000 : ℝ)*(major2) + (3755485393/50000000000000 : ℝ)*(sp1) + (10254398883/100000000000000 : ℝ)*(sp2) + (185336161195619/6250000000000 : ℝ)*(sp4) + (59307405332703/2000000000000 : ℝ)*(sp5) + (370670919300831/12500000000000 : ℝ)*(sp6) + (370597047681351/25000000000000 : ℝ)*(sp7) + (370597047681351/25000000000000 : ℝ)*(f.failure) + (185336161195619/6250000000000 : ℝ)*(f.sum) + (193028068750987/36265000000000000000000000000 : ℝ)*base66 + (2923312175702794599/290120000000000000000000000000000 : ℝ)*base67 + (2914951635639914599/290120000000000000000000000000000 : ℝ)*base69 + (1266770031251514599/290120000000000000000000000000000 : ℝ)*base71 + (62624382619353/36265000000000000000000000000 : ℝ)*base73 + (2479010073541114599/290120000000000000000000000000000 : ℝ)*base75 + (180184174911274599/290120000000000000000000000000000 : ℝ)*base77 + (465880716418605401/290120000000000000000000000000000 : ℝ)*base80 + (7898226682137/9066250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4329113/500000000000000000000 : ℝ)*base89 + (4329113/500000000000000000000 : ℝ)*base91 + (4329113/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1170_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1161/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1839/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (821/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1170_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1170_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1839/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (821/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1170_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1170_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1170_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4181/1024 : ℝ) ≤ p) (hpb : p ≤ (8363/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30004063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1839/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (821/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1170_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
