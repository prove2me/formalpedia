-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1497_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:51:35.320043+00:00
-- url     : https://prove2.me/submissions/8697b483-fb4f-46e5-9aa1-a5817d3d34bd

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
theorem support_rectangle_w1497_s0_0 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-340372173/2000000000 : ℝ)*x 0 + (370279473/625000000 : ℝ)*x 1 + (1212211989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340372173/2000000000 : ℝ)^4491 ≤ (10087247804289/100000000000000 : ℝ)^3467 := by
    have hnat : (340372173 : ℕ)^4491*100000000000000^3467 ≤ 10087247804289^3467*2000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340372173 2000000000 10087247804289 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (370279473/625000000 : ℝ)^4491 ≤ (50757505645909/100000000000000 : ℝ)^3467 := by
    have hnat : (370279473 : ℕ)^4491*100000000000000^3467 ≤ 50757505645909^3467*625000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370279473 625000000 50757505645909 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1212211989/2500000000 : ℝ)^4491 ≤ (19577623269887/50000000000000 : ℝ)^3467 := by
    have hnat : (1212211989 : ℕ)^4491*50000000000000^3467 ≤ 19577623269887^3467*2500000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212211989 2500000000 19577623269887 50000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-340372173/2000000000 : ℝ), (370279473/625000000 : ℝ), (1212211989/2500000000 : ℝ)] ![(10087247804289/100000000000000 : ℝ), (50757505645909/100000000000000 : ℝ), (19577623269887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-340372173/2000000000 : ℝ)|^4491 ≤ (10087247804289/100000000000000 : ℝ)^3467
        have hw : |(-340372173/2000000000 : ℝ)|=(340372173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(370279473/625000000 : ℝ)|^4491 ≤ (50757505645909/100000000000000 : ℝ)^3467
        have hw : |(370279473/625000000 : ℝ)|=(370279473/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1212211989/2500000000 : ℝ)|^4491 ≤ (19577623269887/50000000000000 : ℝ)^3467
        have hw : |(1212211989/2500000000 : ℝ)|=(1212211989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s0_1 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1370312733/2500000000 : ℝ)*x 0 + (-2305943781/10000000000 : ℝ)*x 1 + (1212212107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1370312733/2500000000 : ℝ)^4491 ≤ (1792735469/3906250000 : ℝ)^3467 := by
    have hnat : (1370312733 : ℕ)^4491*3906250000^3467 ≤ 1792735469^3467*2500000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370312733 2500000000 1792735469 3906250000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2305943781/10000000000 : ℝ)^4491 ≤ (14950720501039/100000000000000 : ℝ)^3467 := by
    have hnat : (2305943781 : ℕ)^4491*100000000000000^3467 ≤ 14950720501039^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305943781 10000000000 14950720501039 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1212212107/2500000000 : ℝ)^4491 ≤ (7831050295399/20000000000000 : ℝ)^3467 := by
    have hnat : (1212212107 : ℕ)^4491*20000000000000^3467 ≤ 7831050295399^3467*2500000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212212107 2500000000 7831050295399 20000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1370312733/2500000000 : ℝ), (-2305943781/10000000000 : ℝ), (1212212107/2500000000 : ℝ)] ![(1792735469/3906250000 : ℝ), (14950720501039/100000000000000 : ℝ), (7831050295399/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1370312733/2500000000 : ℝ)|^4491 ≤ (1792735469/3906250000 : ℝ)^3467
        have hw : |(1370312733/2500000000 : ℝ)|=(1370312733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2305943781/10000000000 : ℝ)|^4491 ≤ (14950720501039/100000000000000 : ℝ)^3467
        have hw : |(-2305943781/10000000000 : ℝ)|=(2305943781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1212212107/2500000000 : ℝ)|^4491 ≤ (7831050295399/20000000000000 : ℝ)^3467
        have hw : |(1212212107/2500000000 : ℝ)|=(1212212107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s0_2 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5481250917/10000000000 : ℝ)*x 0 + (2424424931/5000000000 : ℝ)*x 1 + (-1152971007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5481250917/10000000000 : ℝ)^4491 ≤ (358547092529/781250000000 : ℝ)^3467 := by
    have hnat : (5481250917 : ℕ)^4491*781250000000^3467 ≤ 358547092529^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481250917 10000000000 358547092529 781250000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2424424931/5000000000 : ℝ)^4491 ≤ (7831053295389/20000000000000 : ℝ)^3467 := by
    have hnat : (2424424931 : ℕ)^4491*20000000000000^3467 ≤ 7831053295389^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2424424931 5000000000 7831053295389 20000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1152971007/5000000000 : ℝ)^4491 ≤ (14950705660861/100000000000000 : ℝ)^3467 := by
    have hnat : (1152971007 : ℕ)^4491*100000000000000^3467 ≤ 14950705660861^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152971007 5000000000 14950705660861 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5481250917/10000000000 : ℝ), (2424424931/5000000000 : ℝ), (-1152971007/5000000000 : ℝ)] ![(358547092529/781250000000 : ℝ), (7831053295389/20000000000000 : ℝ), (14950705660861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5481250917/10000000000 : ℝ)|^4491 ≤ (358547092529/781250000000 : ℝ)^3467
        have hw : |(5481250917/10000000000 : ℝ)|=(5481250917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2424424931/5000000000 : ℝ)|^4491 ≤ (7831053295389/20000000000000 : ℝ)^3467
        have hw : |(2424424931/5000000000 : ℝ)|=(2424424931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1152971007/5000000000 : ℝ)|^4491 ≤ (14950705660861/100000000000000 : ℝ)^3467
        have hw : |(-1152971007/5000000000 : ℝ)|=(1152971007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s0_3 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (518651571/1250000000 : ℝ)*x 0 + (3091250823/10000000000 : ℝ)*x 1 + (2752277617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518651571/1250000000 : ℝ)^4491 ≤ (31998489299363/100000000000000 : ℝ)^3467 := by
    have hnat : (518651571 : ℕ)^4491*100000000000000^3467 ≤ 31998489299363^3467*1250000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518651571 1250000000 31998489299363 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091250823/10000000000 : ℝ)^4491 ≤ (2731820992823/12500000000000 : ℝ)^3467 := by
    have hnat : (3091250823 : ℕ)^4491*12500000000000^3467 ≤ 2731820992823^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091250823 10000000000 2731820992823 12500000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2752277617/5000000000 : ℝ)^4491 ≤ (5768367842491/12500000000000 : ℝ)^3467 := by
    have hnat : (2752277617 : ℕ)^4491*12500000000000^3467 ≤ 5768367842491^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752277617 5000000000 5768367842491 12500000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518651571/1250000000 : ℝ), (3091250823/10000000000 : ℝ), (2752277617/5000000000 : ℝ)] ![(31998489299363/100000000000000 : ℝ), (2731820992823/12500000000000 : ℝ), (5768367842491/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518651571/1250000000 : ℝ)|^4491 ≤ (31998489299363/100000000000000 : ℝ)^3467
        have hw : |(518651571/1250000000 : ℝ)|=(518651571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091250823/10000000000 : ℝ)|^4491 ≤ (2731820992823/12500000000000 : ℝ)^3467
        have hw : |(3091250823/10000000000 : ℝ)|=(3091250823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2752277617/5000000000 : ℝ)|^4491 ≤ (5768367842491/12500000000000 : ℝ)^3467
        have hw : |(2752277617/5000000000 : ℝ)|=(2752277617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s0_4 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-341101987/2000000000 : ℝ)*x 0 + (975272381/2000000000 : ℝ)*x 1 + (2947985607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341101987/2000000000 : ℝ)^4491 ≤ (5057636784543/50000000000000 : ℝ)^3467 := by
    have hnat : (341101987 : ℕ)^4491*50000000000000^3467 ≤ 5057636784543^3467*2000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341101987 2000000000 5057636784543 50000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (975272381/2000000000 : ℝ)^4491 ≤ (7888657842157/20000000000000 : ℝ)^3467 := by
    have hnat : (975272381 : ℕ)^4491*20000000000000^3467 ≤ 7888657842157^3467*2000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975272381 2000000000 7888657842157 20000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2947985607/5000000000 : ℝ)^4491 ≤ (10088287441907/20000000000000 : ℝ)^3467 := by
    have hnat : (2947985607 : ℕ)^4491*20000000000000^3467 ≤ 10088287441907^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2947985607 5000000000 10088287441907 20000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-341101987/2000000000 : ℝ), (975272381/2000000000 : ℝ), (2947985607/5000000000 : ℝ)] ![(5057636784543/50000000000000 : ℝ), (7888657842157/20000000000000 : ℝ), (10088287441907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-341101987/2000000000 : ℝ)|^4491 ≤ (5057636784543/50000000000000 : ℝ)^3467
        have hw : |(-341101987/2000000000 : ℝ)|=(341101987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(975272381/2000000000 : ℝ)|^4491 ≤ (7888657842157/20000000000000 : ℝ)^3467
        have hw : |(975272381/2000000000 : ℝ)|=(975272381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2947985607/5000000000 : ℝ)|^4491 ≤ (10088287441907/20000000000000 : ℝ)^3467
        have hw : |(2947985607/5000000000 : ℝ)|=(2947985607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s0_5 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5187455311/10000000000 : ℝ)*x 0 + (-629409947/5000000000 : ℝ)*x 1 + (5895971267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5187455311/10000000000 : ℝ)^4491 ≤ (42733097065641/100000000000000 : ℝ)^3467 := by
    have hnat : (5187455311 : ℕ)^4491*100000000000000^3467 ≤ 42733097065641^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187455311 10000000000 42733097065641 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (629409947/5000000000 : ℝ)^4491 ≤ (6825465124907/100000000000000 : ℝ)^3467 := by
    have hnat : (629409947 : ℕ)^4491*100000000000000^3467 ≤ 6825465124907^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629409947 5000000000 6825465124907 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5895971267/10000000000 : ℝ)^4491 ≤ (10088287559377/20000000000000 : ℝ)^3467 := by
    have hnat : (5895971267 : ℕ)^4491*20000000000000^3467 ≤ 10088287559377^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5895971267 10000000000 10088287559377 20000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5187455311/10000000000 : ℝ), (-629409947/5000000000 : ℝ), (5895971267/10000000000 : ℝ)] ![(42733097065641/100000000000000 : ℝ), (6825465124907/100000000000000 : ℝ), (10088287559377/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5187455311/10000000000 : ℝ)|^4491 ≤ (42733097065641/100000000000000 : ℝ)^3467
        have hw : |(5187455311/10000000000 : ℝ)|=(5187455311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-629409947/5000000000 : ℝ)|^4491 ≤ (6825465124907/100000000000000 : ℝ)^3467
        have hw : |(-629409947/5000000000 : ℝ)|=(629409947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5895971267/10000000000 : ℝ)|^4491 ≤ (10088287559377/20000000000000 : ℝ)^3467
        have hw : |(5895971267/10000000000 : ℝ)|=(5895971267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s0_6 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5187455351/10000000000 : ℝ)*x 0 + (736996397/1250000000 : ℝ)*x 1 + (-629409989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5187455351/10000000000 : ℝ)^4491 ≤ (1709323899699/4000000000000 : ℝ)^3467 := by
    have hnat : (5187455351 : ℕ)^4491*4000000000000^3467 ≤ 1709323899699^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187455351 10000000000 1709323899699 4000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (736996397/1250000000 : ℝ)^4491 ≤ (788147449819/1562500000000 : ℝ)^3467 := by
    have hnat : (736996397 : ℕ)^4491*1562500000000^3467 ≤ 788147449819^3467*1250000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736996397 1250000000 788147449819 1562500000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (629409989/5000000000 : ℝ)^4491 ≤ (6825465714887/100000000000000 : ℝ)^3467 := by
    have hnat : (629409989 : ℕ)^4491*100000000000000^3467 ≤ 6825465714887^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629409989 5000000000 6825465714887 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5187455351/10000000000 : ℝ), (736996397/1250000000 : ℝ), (-629409989/5000000000 : ℝ)] ![(1709323899699/4000000000000 : ℝ), (788147449819/1562500000000 : ℝ), (6825465714887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5187455351/10000000000 : ℝ)|^4491 ≤ (1709323899699/4000000000000 : ℝ)^3467
        have hw : |(5187455351/10000000000 : ℝ)|=(5187455351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(736996397/1250000000 : ℝ)|^4491 ≤ (788147449819/1562500000000 : ℝ)^3467
        have hw : |(736996397/1250000000 : ℝ)|=(736996397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-629409989/5000000000 : ℝ)|^4491 ≤ (6825465714887/100000000000000 : ℝ)^3467
        have hw : |(-629409989/5000000000 : ℝ)|=(629409989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s0_7 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4157404211/10000000000 : ℝ)*x 0 + (2721413783/5000000000 : ℝ)*x 1 + (1577596757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4157404211/10000000000 : ℝ)^4491 ≤ (401004316351/1250000000000 : ℝ)^3467 := by
    have hnat : (4157404211 : ℕ)^4491*1250000000000^3467 ≤ 401004316351^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4157404211 10000000000 401004316351 1250000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721413783/5000000000 : ℝ)^4491 ≤ (45477724041413/100000000000000 : ℝ)^3467 := by
    have hnat : (2721413783 : ℕ)^4491*100000000000000^3467 ≤ 45477724041413^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721413783 5000000000 45477724041413 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577596757/5000000000 : ℝ)^4491 ≤ (22441930641827/100000000000000 : ℝ)^3467 := by
    have hnat : (1577596757 : ℕ)^4491*100000000000000^3467 ≤ 22441930641827^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577596757 5000000000 22441930641827 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4157404211/10000000000 : ℝ), (2721413783/5000000000 : ℝ), (1577596757/5000000000 : ℝ)] ![(401004316351/1250000000000 : ℝ), (45477724041413/100000000000000 : ℝ), (22441930641827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4157404211/10000000000 : ℝ)|^4491 ≤ (401004316351/1250000000000 : ℝ)^3467
        have hw : |(4157404211/10000000000 : ℝ)|=(4157404211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721413783/5000000000 : ℝ)|^4491 ≤ (45477724041413/100000000000000 : ℝ)^3467
        have hw : |(2721413783/5000000000 : ℝ)|=(2721413783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577596757/5000000000 : ℝ)|^4491 ≤ (22441930641827/100000000000000 : ℝ)^3467
        have hw : |(1577596757/5000000000 : ℝ)|=(1577596757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1497_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162181901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (329/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (321/1250 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4489/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4489 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4489*1^1024 ≤ 0^1024*1^4489 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4489 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4489/1024 : ℝ) ≤ (225125637405021161/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4489 ≤ (225125637405021161/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4489*12500000000000000000^1024 ≤ 225125637405021161^1024*5^4489 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 225125637405021161 12500000000000000000 4489 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (225125637405021161/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4489/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4489 := by
      have hnat : (1 : ℕ)^1024*1^4489 ≤ 1^4489*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4489 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12725125637405021161/12500000000000000000 : ℝ) ≤ (10040800733372929/10000000000000000 : ℝ) ^ (4489/1024 : ℝ) := by
    have hpowers : (12725125637405021161/12500000000000000000 : ℝ)^1024 ≤ (10040800733372929/10000000000000000 : ℝ)^4489 := by
      have hnat : (12725125637405021161 : ℕ)^1024*10000000000000000^4489 ≤ 10040800733372929^4489*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12725125637405021161 12500000000000000000 10040800733372929 10000000000000000 1024 4489 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10040800733372929/10000000000000000 : ℝ)) (X := (12725125637405021161/12500000000000000000 : ℝ)) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6475125637405021161/6250000000000000000 : ℝ) ≤ (5040800733372929/5000000000000000 : ℝ) ^ (4489/1024 : ℝ) := by
    have hpowers : (6475125637405021161/6250000000000000000 : ℝ)^1024 ≤ (5040800733372929/5000000000000000 : ℝ)^4489 := by
      have hnat : (6475125637405021161 : ℕ)^1024*5000000000000000^4489 ≤ 5040800733372929^4489*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6475125637405021161 6250000000000000000 5040800733372929 5000000000000000 1024 4489 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5040800733372929/5000000000000000 : ℝ)) (X := (6475125637405021161/6250000000000000000 : ℝ)) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(40800733372929/4000000000000000 : ℝ)*(0 : ℝ))^(4489/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(40800733372929/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(225125637405021161/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(40800733372929/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4489/1024 : ℝ) := by
    rw [show (1 : ℝ)+(40800733372929/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10040800733372929/10000000000000000 : ℝ) by norm_num, show 1+(225125637405021161/12500000000000000000 : ℝ)+(0 : ℝ)=(12725125637405021161/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(225125637405021161/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(40800733372929/4000000000000000 : ℝ)*(2/5 : ℝ))^(4489/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(40800733372929/4000000000000000 : ℝ)*(2/5 : ℝ)=(5040800733372929/5000000000000000 : ℝ) by norm_num, show 1+2*(225125637405021161/12500000000000000000 : ℝ)=(6475125637405021161/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(40800733372929/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4489/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40800733372929/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(40800733372929/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4489/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40800733372929/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(40800733372929/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4489/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40800733372929/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-340372173/2000000000 : ℝ)*X 0 0+(370279473/625000000 : ℝ)*X 0 1+(1212211989/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1370312733/2500000000 : ℝ)*X 1 0+(-2305943781/10000000000 : ℝ)*X 1 1+(1212212107/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5481250917/10000000000 : ℝ)*X 2 0+(2424424931/5000000000 : ℝ)*X 2 1+(-1152971007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((518651571/1250000000 : ℝ)*X 0 0+(3091250823/10000000000 : ℝ)*X 0 1+(2752277617/5000000000 : ℝ)*X 0 2+(518651571/1250000000 : ℝ)*X 1 0+(3091250823/10000000000 : ℝ)*X 1 1+(2752277617/5000000000 : ℝ)*X 1 2+(518651571/1250000000 : ℝ)*X 2 0+(3091250823/10000000000 : ℝ)*X 2 1+(2752277617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-341101987/2000000000 : ℝ)*X 0 0+(975272381/2000000000 : ℝ)*X 0 1+(2947985607/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5187455311/10000000000 : ℝ)*X 1 0+(-629409947/5000000000 : ℝ)*X 1 1+(5895971267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5187455351/10000000000 : ℝ)*X 2 0+(736996397/1250000000 : ℝ)*X 2 1+(-629409989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4157404211/10000000000 : ℝ)*X 0 0+(2721413783/5000000000 : ℝ)*X 0 1+(1577596757/5000000000 : ℝ)*X 0 2+(4157404211/10000000000 : ℝ)*X 1 0+(2721413783/5000000000 : ℝ)*X 1 1+(1577596757/5000000000 : ℝ)*X 1 2+(4157404211/10000000000 : ℝ)*X 2 0+(2721413783/5000000000 : ℝ)*X 2 1+(1577596757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (182358901108168135319439/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1590014877/100000000000000 : ℝ)*(base19) + (164406089/12500000000000 : ℝ)*(base23) + (124427609/100000000000000 : ℝ)*(upper3) + (5968467/4000000000000 : ℝ)*(upper4) + (189202907/50000000000000 : ℝ)*(upper5) + (134407843772201/20000000000000 : ℝ)*(major0) + (134407843772201/20000000000000 : ℝ)*(major1) + (134407843772201/20000000000000 : ℝ)*(major2) + (9296974869283/1000000000000 : ℝ)*(sp0) + (929702949523541/100000000000000 : ℝ)*(sp1) + (464851612144853/50000000000000 : ℝ)*(sp2) + (207185973399383/50000000000000 : ℝ)*(sp3) + (3526305059/50000000000000 : ℝ)*(sp4) + (1799419071/100000000000000 : ℝ)*(sp7) + (207186873108919/50000000000000 : ℝ)*(f.failure) + (464852269769209/50000000000000 : ℝ)*(f.sum) + (123725566586729/40000000000000000000000000000 : ℝ)*base65 + (73416527373271/80000000000000000000000000000 : ℝ)*base68 + (173885872946729/80000000000000000000000000000 : ℝ)*base69 + (7037686333271/80000000000000000000000000000 : ℝ)*base72 + (118363572826729/40000000000000000000000000000 : ℝ)*base73 + (41074233266729/80000000000000000000000000000 : ℝ)*base75 + (23044698466729/80000000000000000000000000000 : ℝ)*base77 + (133319837933271/80000000000000000000000000000 : ℝ)*base80 + (254831901986729/40000000000000000000000000000 : ℝ)*base81 + (13475019/5000000000000000000000 : ℝ)*base89 + (13475019/5000000000000000000000 : ℝ)*base91 + (13475019/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1577605491631317394431159/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1753049087/100000000000000 : ℝ)*(base19) + (55412741/3125000000000 : ℝ)*(base23) + (26878903/20000000000000 : ℝ)*(base32) + (264262751/100000000000000 : ℝ)*(upper3) + (88024577/50000000000000 : ℝ)*(upper5) + (708950056103043/100000000000000 : ℝ)*(major0) + (708950056103043/100000000000000 : ℝ)*(major1) + (708950056103043/100000000000000 : ℝ)*(major2) + (2198365271/50000000000000 : ℝ)*(sp1) + (4619135517/100000000000000 : ℝ)*(sp2) + (245191797591851/25000000000000 : ℝ)*(sp4) + (957774453699/97656250000 : ℝ)*(sp5) + (61297549876511/6250000000000 : ℝ)*(sp6) + (43713252450991/10000000000000 : ℝ)*(sp7) + (17485306356177/4000000000000 : ℝ)*(f.failure) + (245191797591851/25000000000000 : ℝ)*(f.sum) + (31211483277053/200000000000000000000000000000 : ℝ)*base66 + (670393498722947/400000000000000000000000000000 : ℝ)*base67 + (3261950092322947/400000000000000000000000000000 : ℝ)*base69 + (590013174722947/400000000000000000000000000000 : ℝ)*base71 + (343702167922947/200000000000000000000000000000 : ℝ)*base73 + (1912374592477053/400000000000000000000000000000 : ℝ)*base76 + (1033523379277053/400000000000000000000000000000 : ℝ)*base78 + (46628505277053/400000000000000000000000000000 : ℝ)*base80 + (1038398095922947/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3047523/400000000000000000000 : ℝ)*base90 + (3047523/400000000000000000000 : ℝ)*base92 + (3047523/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1497_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162181901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (329/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (321/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1497_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1497_s1_0 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-116226067/625000000 : ℝ)*x 0 + (174396763/312500000 : ℝ)*x 1 + (1018259151/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116226067/625000000 : ℝ)^4491 ≤ (5657352317759/50000000000000 : ℝ)^3467 := by
    have hnat : (116226067 : ℕ)^4491*50000000000000^3467 ≤ 5657352317759^3467*625000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116226067 625000000 5657352317759 50000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174396763/312500000 : ℝ)^4491 ≤ (1467983801941/3125000000000 : ℝ)^3467 := by
    have hnat : (174396763 : ℕ)^4491*3125000000000^3467 ≤ 1467983801941^3467*312500000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174396763 312500000 1467983801941 3125000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1018259151/2000000000 : ℝ)^4491 ≤ (521372671081/1250000000000 : ℝ)^3467 := by
    have hnat : (1018259151 : ℕ)^4491*1250000000000^3467 ≤ 521372671081^3467*2000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018259151 2000000000 521372671081 1250000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116226067/625000000 : ℝ), (174396763/312500000 : ℝ), (1018259151/2000000000 : ℝ)] ![(5657352317759/50000000000000 : ℝ), (1467983801941/3125000000000 : ℝ), (521372671081/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116226067/625000000 : ℝ)|^4491 ≤ (5657352317759/50000000000000 : ℝ)^3467
        have hw : |(-116226067/625000000 : ℝ)|=(116226067/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(174396763/312500000 : ℝ)|^4491 ≤ (1467983801941/3125000000000 : ℝ)^3467
        have hw : |(174396763/312500000 : ℝ)|=(174396763/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1018259151/2000000000 : ℝ)|^4491 ≤ (521372671081/1250000000000 : ℝ)^3467
        have hw : |(1018259151/2000000000 : ℝ)|=(1018259151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s1_1 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389380261/10000000000 : ℝ)*x 0 + (-2117810479/10000000000 : ℝ)*x 1 + (5091296471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389380261/10000000000 : ℝ)^4491 ≤ (44900083781511/100000000000000 : ℝ)^3467 := by
    have hnat : (5389380261 : ℕ)^4491*100000000000000^3467 ≤ 44900083781511^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389380261 10000000000 44900083781511 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117810479/10000000000 : ℝ)^4491 ≤ (13390094919529/100000000000000 : ℝ)^3467 := by
    have hnat : (2117810479 : ℕ)^4491*100000000000000^3467 ≤ 13390094919529^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117810479 10000000000 13390094919529 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5091296471/10000000000 : ℝ)^4491 ≤ (8341964256941/20000000000000 : ℝ)^3467 := by
    have hnat : (5091296471 : ℕ)^4491*20000000000000^3467 ≤ 8341964256941^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5091296471 10000000000 8341964256941 20000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389380261/10000000000 : ℝ), (-2117810479/10000000000 : ℝ), (5091296471/10000000000 : ℝ)] ![(44900083781511/100000000000000 : ℝ), (13390094919529/100000000000000 : ℝ), (8341964256941/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389380261/10000000000 : ℝ)|^4491 ≤ (44900083781511/100000000000000 : ℝ)^3467
        have hw : |(5389380261/10000000000 : ℝ)|=(5389380261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2117810479/10000000000 : ℝ)|^4491 ≤ (13390094919529/100000000000000 : ℝ)^3467
        have hw : |(-2117810479/10000000000 : ℝ)|=(2117810479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5091296471/10000000000 : ℝ)|^4491 ≤ (8341964256941/20000000000000 : ℝ)^3467
        have hw : |(5091296471/10000000000 : ℝ)|=(5091296471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s1_2 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347345221/2500000000 : ℝ)*x 0 + (636412009/1250000000 : ℝ)*x 1 + (-2068174/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347345221/2500000000 : ℝ)^4491 ≤ (44900090504859/100000000000000 : ℝ)^3467 := by
    have hnat : (1347345221 : ℕ)^4491*100000000000000^3467 ≤ 44900090504859^3467*2500000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347345221 2500000000 44900090504859 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (636412009/1250000000 : ℝ)^4491 ≤ (41709817050499/100000000000000 : ℝ)^3467 := by
    have hnat : (636412009 : ℕ)^4491*100000000000000^3467 ≤ 41709817050499^3467*1250000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636412009 1250000000 41709817050499 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068174/9765625 : ℝ)^4491 ≤ (13390092437949/100000000000000 : ℝ)^3467 := by
    have hnat : (2068174 : ℕ)^4491*100000000000000^3467 ≤ 13390092437949^3467*9765625^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068174 9765625 13390092437949 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347345221/2500000000 : ℝ), (636412009/1250000000 : ℝ), (-2068174/9765625 : ℝ)] ![(44900090504859/100000000000000 : ℝ), (41709817050499/100000000000000 : ℝ), (13390092437949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347345221/2500000000 : ℝ)|^4491 ≤ (44900090504859/100000000000000 : ℝ)^3467
        have hw : |(1347345221/2500000000 : ℝ)|=(1347345221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(636412009/1250000000 : ℝ)|^4491 ≤ (41709817050499/100000000000000 : ℝ)^3467
        have hw : |(636412009/1250000000 : ℝ)|=(636412009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2068174/9765625 : ℝ)|^4491 ≤ (13390092437949/100000000000000 : ℝ)^3467
        have hw : |(-2068174/9765625 : ℝ)|=(2068174/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s1_3 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4255079511/10000000000 : ℝ)*x 0 + (3736336217/10000000000 : ℝ)*x 1 + (604296669/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4255079511/10000000000 : ℝ)^4491 ≤ (6612006198807/20000000000000 : ℝ)^3467 := by
    have hnat : (4255079511 : ℕ)^4491*20000000000000^3467 ≤ 6612006198807^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255079511 10000000000 6612006198807 20000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3736336217/10000000000 : ℝ)^4491 ≤ (27936063119529/100000000000000 : ℝ)^3467 := by
    have hnat : (3736336217 : ℕ)^4491*100000000000000^3467 ≤ 27936063119529^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3736336217 10000000000 27936063119529 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (604296669/1250000000 : ℝ)^4491 ≤ (39003905864133/100000000000000 : ℝ)^3467 := by
    have hnat : (604296669 : ℕ)^4491*100000000000000^3467 ≤ 39003905864133^3467*1250000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604296669 1250000000 39003905864133 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4255079511/10000000000 : ℝ), (3736336217/10000000000 : ℝ), (604296669/1250000000 : ℝ)] ![(6612006198807/20000000000000 : ℝ), (27936063119529/100000000000000 : ℝ), (39003905864133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4255079511/10000000000 : ℝ)|^4491 ≤ (6612006198807/20000000000000 : ℝ)^3467
        have hw : |(4255079511/10000000000 : ℝ)|=(4255079511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3736336217/10000000000 : ℝ)|^4491 ≤ (27936063119529/100000000000000 : ℝ)^3467
        have hw : |(3736336217/10000000000 : ℝ)|=(3736336217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(604296669/1250000000 : ℝ)|^4491 ≤ (39003905864133/100000000000000 : ℝ)^3467
        have hw : |(604296669/1250000000 : ℝ)|=(604296669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s1_4 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-929974281/5000000000 : ℝ)*x 0 + (2548443239/5000000000 : ℝ)*x 1 + (2787506929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929974281/5000000000 : ℝ)^4491 ≤ (1131731734291/10000000000000 : ℝ)^3467 := by
    have hnat : (929974281 : ℕ)^4491*10000000000000^3467 ≤ 1131731734291^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929974281 5000000000 1131731734291 10000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2548443239/5000000000 : ℝ)^4491 ≤ (5221144039567/12500000000000 : ℝ)^3467 := by
    have hnat : (2548443239 : ℕ)^4491*12500000000000^3467 ≤ 5221144039567^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548443239 5000000000 5221144039567 12500000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2787506929/5000000000 : ℝ)^4491 ≤ (11728382583993/25000000000000 : ℝ)^3467 := by
    have hnat : (2787506929 : ℕ)^4491*25000000000000^3467 ≤ 11728382583993^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2787506929 5000000000 11728382583993 25000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-929974281/5000000000 : ℝ), (2548443239/5000000000 : ℝ), (2787506929/5000000000 : ℝ)] ![(1131731734291/10000000000000 : ℝ), (5221144039567/12500000000000 : ℝ), (11728382583993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-929974281/5000000000 : ℝ)|^4491 ≤ (1131731734291/10000000000000 : ℝ)^3467
        have hw : |(-929974281/5000000000 : ℝ)|=(929974281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2548443239/5000000000 : ℝ)|^4491 ≤ (5221144039567/12500000000000 : ℝ)^3467
        have hw : |(2548443239/5000000000 : ℝ)|=(2548443239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2787506929/5000000000 : ℝ)|^4491 ≤ (11728382583993/25000000000000 : ℝ)^3467
        have hw : |(2787506929/5000000000 : ℝ)|=(2787506929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s1_5 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260712951/10000000000 : ℝ)*x 0 + (-1634092679/10000000000 : ℝ)*x 1 + (557501397/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260712951/10000000000 : ℝ)^4491 ≤ (10879110908497/25000000000000 : ℝ)^3467 := by
    have hnat : (5260712951 : ℕ)^4491*25000000000000^3467 ≤ 10879110908497^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260712951 10000000000 10879110908497 25000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1634092679/10000000000 : ℝ)^4491 ≤ (478501239667/5000000000000 : ℝ)^3467 := by
    have hnat : (1634092679 : ℕ)^4491*5000000000000^3467 ≤ 478501239667^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1634092679 10000000000 478501239667 5000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (557501397/1000000000 : ℝ)^4491 ≤ (23456765778407/50000000000000 : ℝ)^3467 := by
    have hnat : (557501397 : ℕ)^4491*50000000000000^3467 ≤ 23456765778407^3467*1000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557501397 1000000000 23456765778407 50000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260712951/10000000000 : ℝ), (-1634092679/10000000000 : ℝ), (557501397/1000000000 : ℝ)] ![(10879110908497/25000000000000 : ℝ), (478501239667/5000000000000 : ℝ), (23456765778407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260712951/10000000000 : ℝ)|^4491 ≤ (10879110908497/25000000000000 : ℝ)^3467
        have hw : |(5260712951/10000000000 : ℝ)|=(5260712951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1634092679/10000000000 : ℝ)|^4491 ≤ (478501239667/5000000000000 : ℝ)^3467
        have hw : |(-1634092679/10000000000 : ℝ)|=(1634092679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(557501397/1000000000 : ℝ)|^4491 ≤ (23456765778407/50000000000000 : ℝ)^3467
        have hw : |(557501397/1000000000 : ℝ)|=(557501397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s1_6 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260712861/10000000000 : ℝ)*x 0 + (1393753497/2500000000 : ℝ)*x 1 + (-81704639/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260712861/10000000000 : ℝ)^4491 ≤ (348131541357/800000000000 : ℝ)^3467 := by
    have hnat : (5260712861 : ℕ)^4491*800000000000^3467 ≤ 348131541357^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260712861 10000000000 348131541357 800000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1393753497/2500000000 : ℝ)^4491 ≤ (46913531753021/100000000000000 : ℝ)^3467 := by
    have hnat : (1393753497 : ℕ)^4491*100000000000000^3467 ≤ 46913531753021^3467*2500000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393753497 2500000000 46913531753021 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81704639/500000000 : ℝ)^4491 ≤ (9570025559549/100000000000000 : ℝ)^3467 := by
    have hnat : (81704639 : ℕ)^4491*100000000000000^3467 ≤ 9570025559549^3467*500000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81704639 500000000 9570025559549 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260712861/10000000000 : ℝ), (1393753497/2500000000 : ℝ), (-81704639/500000000 : ℝ)] ![(348131541357/800000000000 : ℝ), (46913531753021/100000000000000 : ℝ), (9570025559549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260712861/10000000000 : ℝ)|^4491 ≤ (348131541357/800000000000 : ℝ)^3467
        have hw : |(5260712861/10000000000 : ℝ)|=(5260712861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1393753497/2500000000 : ℝ)|^4491 ≤ (46913531753021/100000000000000 : ℝ)^3467
        have hw : |(1393753497/2500000000 : ℝ)|=(1393753497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-81704639/500000000 : ℝ)|^4491 ≤ (9570025559549/100000000000000 : ℝ)^3467
        have hw : |(-81704639/500000000 : ℝ)|=(81704639/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s1_7 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2127911897/5000000000 : ℝ)*x 0 + (482183099/1000000000 : ℝ)*x 1 + (937271307/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127911897/5000000000 : ℝ)^4491 ≤ (6613504379179/20000000000000 : ℝ)^3467 := by
    have hnat : (2127911897 : ℕ)^4491*20000000000000^3467 ≤ 6613504379179^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127911897 5000000000 6613504379179 20000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482183099/1000000000 : ℝ)^4491 ≤ (38872876109181/100000000000000 : ℝ)^3467 := by
    have hnat : (482183099 : ℕ)^4491*100000000000000^3467 ≤ 38872876109181^3467*1000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482183099 1000000000 38872876109181 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937271307/2500000000 : ℝ)^4491 ≤ (7014900493849/25000000000000 : ℝ)^3467 := by
    have hnat : (937271307 : ℕ)^4491*25000000000000^3467 ≤ 7014900493849^3467*2500000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937271307 2500000000 7014900493849 25000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127911897/5000000000 : ℝ), (482183099/1000000000 : ℝ), (937271307/2500000000 : ℝ)] ![(6613504379179/20000000000000 : ℝ), (38872876109181/100000000000000 : ℝ), (7014900493849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127911897/5000000000 : ℝ)|^4491 ≤ (6613504379179/20000000000000 : ℝ)^3467
        have hw : |(2127911897/5000000000 : ℝ)|=(2127911897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(482183099/1000000000 : ℝ)|^4491 ≤ (38872876109181/100000000000000 : ℝ)^3467
        have hw : |(482183099/1000000000 : ℝ)|=(482183099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(937271307/2500000000 : ℝ)|^4491 ≤ (7014900493849/25000000000000 : ℝ)^3467
        have hw : |(937271307/2500000000 : ℝ)|=(937271307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1497_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162181901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (321/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (329/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (163/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18499/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (321/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (329/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (321/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (329/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (321/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (329/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (321/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (329/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (321/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (329/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (321/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (329/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (329/12500 : ℝ) ^ (4489/1024 : ℝ) ≤ (11881370546959/100000000000000000000 : ℝ) := by
    have hpowers : (329/12500 : ℝ)^4489 ≤ (11881370546959/100000000000000000000 : ℝ)^1024 := by
      have hnat : (329 : ℕ)^4489*100000000000000000000^1024 ≤ 11881370546959^1024*12500^4489 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        329 12500 11881370546959 100000000000000000000 4489 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (329/12500 : ℝ)) (X := (11881370546959/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (321/1250 : ℝ) ^ (4489/1024 : ℝ) ≤ (258100653158641573/100000000000000000000 : ℝ) := by
    have hpowers : (321/1250 : ℝ)^4489 ≤ (258100653158641573/100000000000000000000 : ℝ)^1024 := by
      have hnat : (321 : ℕ)^4489*100000000000000000000^1024 ≤ 258100653158641573^1024*1250^4489 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        321 1250 258100653158641573 100000000000000000000 4489 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (321/1250 : ℝ)) (X := (258100653158641573/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000011881370546959/50000000000000000000 : ℝ) ≤ (62500003387871/62500000000000 : ℝ) ^ (4489/1024 : ℝ) := by
    have hpowers : (50000011881370546959/50000000000000000000 : ℝ)^1024 ≤ (62500003387871/62500000000000 : ℝ)^4489 := by
      have hnat : (50000011881370546959 : ℕ)^1024*62500000000000^4489 ≤ 62500003387871^4489*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000011881370546959 50000000000000000000 62500003387871 62500000000000 1024 4489 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62500003387871/62500000000000 : ℝ)) (X := (50000011881370546959/50000000000000000000 : ℝ)) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25064528133632297133/25000000000000000000 : ℝ) ≤ (10005882030330399/10000000000000000 : ℝ) ^ (4489/1024 : ℝ) := by
    have hpowers : (25064528133632297133/25000000000000000000 : ℝ)^1024 ≤ (10005882030330399/10000000000000000 : ℝ)^4489 := by
      have hnat : (25064528133632297133 : ℕ)^1024*10000000000000000^4489 ≤ 10005882030330399^4489*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25064528133632297133 25000000000000000000 10005882030330399 10000000000000000 1024 4489 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005882030330399/10000000000000000 : ℝ)) (X := (25064528133632297133/25000000000000000000 : ℝ)) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50258100653158641573/50000000000000000000 : ℝ) ≤ (5005881759300719/5000000000000000 : ℝ) ^ (4489/1024 : ℝ) := by
    have hpowers : (50258100653158641573/50000000000000000000 : ℝ)^1024 ≤ (5005881759300719/5000000000000000 : ℝ)^4489 := by
      have hnat : (50258100653158641573 : ℕ)^1024*5000000000000000^4489 ≤ 5005881759300719^4489*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50258100653158641573 50000000000000000000 5005881759300719 5000000000000000 1024 4489 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005881759300719/5000000000000000 : ℝ)) (X := (50258100653158641573/50000000000000000000 : ℝ)) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(11881370546959/100000000000000000000 : ℝ) ≤ ((14403065771195336249/14405000000000000000 : ℝ)+2*(5881488271039/2304800000000000 : ℝ)*(329/12500 : ℝ))^(4489/1024 : ℝ) := by
    rw [show (14403065771195336249/14405000000000000000 : ℝ)+2*(5881488271039/2304800000000000 : ℝ)*(329/12500 : ℝ)=(62500003387871/62500000000000 : ℝ) by norm_num, show 1+2*(11881370546959/100000000000000000000 : ℝ)=(50000011881370546959/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(258100653158641573/100000000000000000000 : ℝ)+(11881370546959/100000000000000000000 : ℝ) ≤ ((14403065771195336249/14405000000000000000 : ℝ)+(5881488271039/2304800000000000 : ℝ)*((321/1250 : ℝ)+(329/12500 : ℝ)))^(4489/1024 : ℝ) := by
    rw [show (14403065771195336249/14405000000000000000 : ℝ)+(5881488271039/2304800000000000 : ℝ)*((321/1250 : ℝ)+(329/12500 : ℝ))=(10005882030330399/10000000000000000 : ℝ) by norm_num, show 1+(258100653158641573/100000000000000000000 : ℝ)+(11881370546959/100000000000000000000 : ℝ)=(25064528133632297133/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(258100653158641573/100000000000000000000 : ℝ) ≤ ((14403065771195336249/14405000000000000000 : ℝ)+2*(5881488271039/2304800000000000 : ℝ)*(321/1250 : ℝ))^(4489/1024 : ℝ) := by
    rw [show (14403065771195336249/14405000000000000000 : ℝ)+2*(5881488271039/2304800000000000 : ℝ)*(321/1250 : ℝ)=(5005881759300719/5000000000000000 : ℝ) by norm_num, show 1+2*(258100653158641573/100000000000000000000 : ℝ)=(50258100653158641573/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14403065771195336249/14405000000000000000 : ℝ)*(X 1 0+X 2 0)+(5881488271039/2304800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4489/1024 : ℝ)) (lo := (329/12500 : ℝ)) (hi := (321/1250 : ℝ)) (c := (14403065771195336249/14405000000000000000 : ℝ)) (alpha := (5881488271039/2304800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14403065771195336249/14405000000000000000 : ℝ)*(X 0 1+X 2 1)+(5881488271039/2304800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4489/1024 : ℝ)) (lo := (329/12500 : ℝ)) (hi := (321/1250 : ℝ)) (c := (14403065771195336249/14405000000000000000 : ℝ)) (alpha := (5881488271039/2304800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14403065771195336249/14405000000000000000 : ℝ)*(X 0 2+X 1 2)+(5881488271039/2304800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4489/1024 : ℝ)) (lo := (329/12500 : ℝ)) (hi := (321/1250 : ℝ)) (c := (14403065771195336249/14405000000000000000 : ℝ)) (alpha := (5881488271039/2304800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-116226067/625000000 : ℝ)*X 0 0+(174396763/312500000 : ℝ)*X 0 1+(1018259151/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5389380261/10000000000 : ℝ)*X 1 0+(-2117810479/10000000000 : ℝ)*X 1 1+(5091296471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1347345221/2500000000 : ℝ)*X 2 0+(636412009/1250000000 : ℝ)*X 2 1+(-2068174/9765625 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4255079511/10000000000 : ℝ)*X 0 0+(3736336217/10000000000 : ℝ)*X 0 1+(604296669/1250000000 : ℝ)*X 0 2+(4255079511/10000000000 : ℝ)*X 1 0+(3736336217/10000000000 : ℝ)*X 1 1+(604296669/1250000000 : ℝ)*X 1 2+(4255079511/10000000000 : ℝ)*X 2 0+(3736336217/10000000000 : ℝ)*X 2 1+(604296669/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-929974281/5000000000 : ℝ)*X 0 0+(2548443239/5000000000 : ℝ)*X 0 1+(2787506929/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260712951/10000000000 : ℝ)*X 1 0+(-1634092679/10000000000 : ℝ)*X 1 1+(557501397/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5260712861/10000000000 : ℝ)*X 2 0+(1393753497/2500000000 : ℝ)*X 2 1+(-81704639/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2127911897/5000000000 : ℝ)*X 0 0+(482183099/1000000000 : ℝ)*X 0 1+(937271307/2500000000 : ℝ)*X 0 2+(2127911897/5000000000 : ℝ)*X 1 0+(482183099/1000000000 : ℝ)*X 1 1+(937271307/2500000000 : ℝ)*X 1 2+(2127911897/5000000000 : ℝ)*X 2 0+(482183099/1000000000 : ℝ)*X 2 1+(937271307/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1028193724580036743166757381/144050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (389764643/25000000000000 : ℝ)*(base19) + (354767627/20000000000000 : ℝ)*(base23) + (107935433/100000000000000 : ℝ)*(upper3) + (360857/3125000000000 : ℝ)*(upper4) + (36074081/12500000000000 : ℝ)*(upper5) + (295407414002123/20000000000000 : ℝ)*(major0) + (295407414002123/20000000000000 : ℝ)*(major1) + (295407414002123/20000000000000 : ℝ)*(major2) + (2043328617764653/100000000000000 : ℝ)*(sp0) + (2043343673005029/100000000000000 : ℝ)*(sp1) + (1021671729112733/50000000000000 : ℝ)*(sp2) + (227680651116473/25000000000000 : ℝ)*(sp3) + (4153574737/25000000000000 : ℝ)*(sp4) + (303278327/5000000000000 : ℝ)*(sp7) + (56920541877027/6250000000000 : ℝ)*(f.failure) + (2043345232063601/100000000000000 : ℝ)*(f.sum) + (85574180417643/23048000000000000000000000000 : ℝ)*base66 + (1624737232090012123/288100000000000000000000000000000 : ℝ)*base68 + (560715456719287877/288100000000000000000000000000000 : ℝ)*base69 + (996918408388512123/288100000000000000000000000000000 : ℝ)*base72 + (128486410204307/23048000000000000000000000000 : ℝ)*base74 + (373397659513287877/288100000000000000000000000000000 : ℝ)*base75 + (183341114326012123/288100000000000000000000000000000 : ℝ)*base78 + (1249274007046012123/288100000000000000000000000000000 : ℝ)*base80 + (24053255715573/23048000000000000000000000000 : ℝ)*base81 + (3338327/625000000000000000000 : ℝ)*base89 + (3338327/625000000000000000000 : ℝ)*base91 + (3338327/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61176285167425836370748661/9003125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130972317/10000000000000 : ℝ)*(base19) + (21243661/1562500000000 : ℝ)*(base23) + (23862759/12500000000000 : ℝ)*(upper3) + (35407759/100000000000000 : ℝ)*(lower4) + (54656489/50000000000000 : ℝ)*(upper5) + (151183960994077/10000000000000 : ℝ)*(major0) + (151183960994077/10000000000000 : ℝ)*(major1) + (151183960994077/10000000000000 : ℝ)*(major2) + (4259441781/50000000000000 : ℝ)*(sp1) + (4634469523/50000000000000 : ℝ)*(sp2) + (1045745684551683/50000000000000 : ℝ)*(sp4) + (1045740770248317/50000000000000 : ℝ)*(sp5) + (65358773142813/3125000000000 : ℝ)*(sp6) + (932187624277983/100000000000000 : ℝ)*(sp7) + (932187624277983/100000000000000 : ℝ)*(f.failure) + (1045745684551683/50000000000000 : ℝ)*(f.sum) + (34225553793563/11524000000000000000000000000 : ℝ)*base65 + (114694715360484077/144050000000000000000000000000000 : ℝ)*base68 + (1025436872408184077/144050000000000000000000000000000 : ℝ)*base70 + (592915650660484077/144050000000000000000000000000000 : ℝ)*base72 + (24137021539339/11524000000000000000000000000 : ℝ)*base73 + (1057571383115923/144050000000000000000000000000000 : ℝ)*base75 + (428683644107684077/144050000000000000000000000000000 : ℝ)*base78 + (352510630437084077/144050000000000000000000000000000 : ℝ)*base80 + (39040013311149/11524000000000000000000000000 : ℝ)*base82 + (35385683/10000000000000000000000 : ℝ)*base89 + (35385683/10000000000000000000000 : ℝ)*base91 + (35385683/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1497_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162181901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (321/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (329/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (163/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18499/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1497_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1497_s2_0 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1885914379/10000000000 : ℝ)*x 0 + (5462883267/10000000000 : ℝ)*x 1 + (519210211/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885914379/10000000000 : ℝ)^4491 ≤ (11522398282753/100000000000000 : ℝ)^3467 := by
    have hnat : (1885914379 : ℕ)^4491*100000000000000^3467 ≤ 11522398282753^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885914379 10000000000 11522398282753 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462883267/10000000000 : ℝ)^4491 ≤ (45694912760969/100000000000000 : ℝ)^3467 := by
    have hnat : (5462883267 : ℕ)^4491*100000000000000^3467 ≤ 45694912760969^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462883267 10000000000 45694912760969 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519210211/1000000000 : ℝ)^4491 ≤ (4278268894159/10000000000000 : ℝ)^3467 := by
    have hnat : (519210211 : ℕ)^4491*10000000000000^3467 ≤ 4278268894159^3467*1000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519210211 1000000000 4278268894159 10000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1885914379/10000000000 : ℝ), (5462883267/10000000000 : ℝ), (519210211/1000000000 : ℝ)] ![(11522398282753/100000000000000 : ℝ), (45694912760969/100000000000000 : ℝ), (4278268894159/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1885914379/10000000000 : ℝ)|^4491 ≤ (11522398282753/100000000000000 : ℝ)^3467
        have hw : |(-1885914379/10000000000 : ℝ)|=(1885914379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462883267/10000000000 : ℝ)|^4491 ≤ (45694912760969/100000000000000 : ℝ)^3467
        have hw : |(5462883267/10000000000 : ℝ)|=(5462883267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519210211/1000000000 : ℝ)|^4491 ≤ (4278268894159/10000000000000 : ℝ)^3467
        have hw : |(519210211/1000000000 : ℝ)|=(519210211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s2_1 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679794789/5000000000 : ℝ)*x 0 + (-2025436011/10000000000 : ℝ)*x 1 + (519210149/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679794789/5000000000 : ℝ)^4491 ≤ (44578848772273/100000000000000 : ℝ)^3467 := by
    have hnat : (2679794789 : ℕ)^4491*100000000000000^3467 ≤ 44578848772273^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679794789 5000000000 44578848772273 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2025436011/10000000000 : ℝ)^4491 ≤ (3159617222157/25000000000000 : ℝ)^3467 := by
    have hnat : (2025436011 : ℕ)^4491*25000000000000^3467 ≤ 3159617222157^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025436011 10000000000 3159617222157 25000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519210149/1000000000 : ℝ)^4491 ≤ (42782682323911/100000000000000 : ℝ)^3467 := by
    have hnat : (519210149 : ℕ)^4491*100000000000000^3467 ≤ 42782682323911^3467*1000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519210149 1000000000 42782682323911 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679794789/5000000000 : ℝ), (-2025436011/10000000000 : ℝ), (519210149/1000000000 : ℝ)] ![(44578848772273/100000000000000 : ℝ), (3159617222157/25000000000000 : ℝ), (42782682323911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679794789/5000000000 : ℝ)|^4491 ≤ (44578848772273/100000000000000 : ℝ)^3467
        have hw : |(2679794789/5000000000 : ℝ)|=(2679794789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2025436011/10000000000 : ℝ)|^4491 ≤ (3159617222157/25000000000000 : ℝ)^3467
        have hw : |(-2025436011/10000000000 : ℝ)|=(2025436011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519210149/1000000000 : ℝ)|^4491 ≤ (42782682323911/100000000000000 : ℝ)^3467
        have hw : |(519210149/1000000000 : ℝ)|=(519210149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s2_2 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679794747/5000000000 : ℝ)*x 0 + (2596050693/5000000000 : ℝ)*x 1 + (-101271813/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679794747/5000000000 : ℝ)^4491 ≤ (44578847867237/100000000000000 : ℝ)^3467 := by
    have hnat : (2679794747 : ℕ)^4491*100000000000000^3467 ≤ 44578847867237^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679794747 5000000000 44578847867237 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596050693/5000000000 : ℝ)^4491 ≤ (5347835151731/12500000000000 : ℝ)^3467 := by
    have hnat : (2596050693 : ℕ)^4491*12500000000000^3467 ≤ 5347835151731^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596050693 5000000000 5347835151731 12500000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101271813/500000000 : ℝ)^4491 ≤ (631923545063/5000000000000 : ℝ)^3467 := by
    have hnat : (101271813 : ℕ)^4491*5000000000000^3467 ≤ 631923545063^3467*500000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101271813 500000000 631923545063 5000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679794747/5000000000 : ℝ), (2596050693/5000000000 : ℝ), (-101271813/500000000 : ℝ)] ![(44578847867237/100000000000000 : ℝ), (5347835151731/12500000000000 : ℝ), (631923545063/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679794747/5000000000 : ℝ)|^4491 ≤ (44578847867237/100000000000000 : ℝ)^3467
        have hw : |(2679794747/5000000000 : ℝ)|=(2679794747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596050693/5000000000 : ℝ)|^4491 ≤ (5347835151731/12500000000000 : ℝ)^3467
        have hw : |(2596050693/5000000000 : ℝ)|=(2596050693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-101271813/500000000 : ℝ)|^4491 ≤ (631923545063/5000000000000 : ℝ)^3467
        have hw : |(-101271813/500000000 : ℝ)|=(101271813/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s2_3 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273905901/10000000000 : ℝ)*x 0 + (248713083/625000000 : ℝ)*x 1 + (2293472167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273905901/10000000000 : ℝ)^4491 ≤ (1039050926093/3125000000000 : ℝ)^3467 := by
    have hnat : (4273905901 : ℕ)^4491*3125000000000^3467 ≤ 1039050926093^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273905901 10000000000 1039050926093 3125000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248713083/625000000 : ℝ)^4491 ≤ (6062511136633/20000000000000 : ℝ)^3467 := by
    have hnat : (248713083 : ℕ)^4491*20000000000000^3467 ≤ 6062511136633^3467*625000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248713083 625000000 6062511136633 20000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2293472167/5000000000 : ℝ)^4491 ≤ (7287562933261/20000000000000 : ℝ)^3467 := by
    have hnat : (2293472167 : ℕ)^4491*20000000000000^3467 ≤ 7287562933261^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293472167 5000000000 7287562933261 20000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273905901/10000000000 : ℝ), (248713083/625000000 : ℝ), (2293472167/5000000000 : ℝ)] ![(1039050926093/3125000000000 : ℝ), (6062511136633/20000000000000 : ℝ), (7287562933261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273905901/10000000000 : ℝ)|^4491 ≤ (1039050926093/3125000000000 : ℝ)^3467
        have hw : |(4273905901/10000000000 : ℝ)|=(4273905901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(248713083/625000000 : ℝ)|^4491 ≤ (6062511136633/20000000000000 : ℝ)^3467
        have hw : |(248713083/625000000 : ℝ)|=(248713083/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2293472167/5000000000 : ℝ)|^4491 ≤ (7287562933261/20000000000000 : ℝ)^3467
        have hw : |(2293472167/5000000000 : ℝ)|=(2293472167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s2_4 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-942984639/5000000000 : ℝ)*x 0 + (1298455951/2500000000 : ℝ)*x 1 + (5461146967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (942984639/5000000000 : ℝ)^4491 ≤ (11522832769391/100000000000000 : ℝ)^3467 := by
    have hnat : (942984639 : ℕ)^4491*100000000000000^3467 ≤ 11522832769391^3467*5000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942984639 5000000000 11522832769391 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298455951/2500000000 : ℝ)^4491 ≤ (10700266661867/25000000000000 : ℝ)^3467 := by
    have hnat : (1298455951 : ℕ)^4491*25000000000000^3467 ≤ 10700266661867^3467*2500000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298455951 2500000000 10700266661867 25000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461146967/10000000000 : ℝ)^4491 ≤ (9135220112741/20000000000000 : ℝ)^3467 := by
    have hnat : (5461146967 : ℕ)^4491*20000000000000^3467 ≤ 9135220112741^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461146967 10000000000 9135220112741 20000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-942984639/5000000000 : ℝ), (1298455951/2500000000 : ℝ), (5461146967/10000000000 : ℝ)] ![(11522832769391/100000000000000 : ℝ), (10700266661867/25000000000000 : ℝ), (9135220112741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-942984639/5000000000 : ℝ)|^4491 ≤ (11522832769391/100000000000000 : ℝ)^3467
        have hw : |(-942984639/5000000000 : ℝ)|=(942984639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1298455951/2500000000 : ℝ)|^4491 ≤ (10700266661867/25000000000000 : ℝ)^3467
        have hw : |(1298455951/2500000000 : ℝ)|=(1298455951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461146967/10000000000 : ℝ)|^4491 ≤ (9135220112741/20000000000000 : ℝ)^3467
        have hw : |(5461146967/10000000000 : ℝ)|=(5461146967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s2_5 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322162197/2500000000 : ℝ)*x 0 + (-1756390081/10000000000 : ℝ)*x 1 + (1092229491/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322162197/2500000000 : ℝ)^4491 ≤ (43816014595553/100000000000000 : ℝ)^3467 := by
    have hnat : (1322162197 : ℕ)^4491*100000000000000^3467 ≤ 43816014595553^3467*2500000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322162197 2500000000 43816014595553 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1756390081/10000000000 : ℝ)^4491 ≤ (2626969886739/25000000000000 : ℝ)^3467 := by
    have hnat : (1756390081 : ℕ)^4491*25000000000000^3467 ≤ 2626969886739^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756390081 10000000000 2626969886739 25000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092229491/2000000000 : ℝ)^4491 ≤ (11419026462691/25000000000000 : ℝ)^3467 := by
    have hnat : (1092229491 : ℕ)^4491*25000000000000^3467 ≤ 11419026462691^3467*2000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092229491 2000000000 11419026462691 25000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322162197/2500000000 : ℝ), (-1756390081/10000000000 : ℝ), (1092229491/2000000000 : ℝ)] ![(43816014595553/100000000000000 : ℝ), (2626969886739/25000000000000 : ℝ), (11419026462691/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322162197/2500000000 : ℝ)|^4491 ≤ (43816014595553/100000000000000 : ℝ)^3467
        have hw : |(1322162197/2500000000 : ℝ)|=(1322162197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1756390081/10000000000 : ℝ)|^4491 ≤ (2626969886739/25000000000000 : ℝ)^3467
        have hw : |(-1756390081/10000000000 : ℝ)|=(1756390081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092229491/2000000000 : ℝ)|^4491 ≤ (11419026462691/25000000000000 : ℝ)^3467
        have hw : |(1092229491/2000000000 : ℝ)|=(1092229491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s2_6 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288648291/10000000000 : ℝ)*x 0 + (5461146567/10000000000 : ℝ)*x 1 + (-1756392009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288648291/10000000000 : ℝ)^4491 ≤ (4381600926179/10000000000000 : ℝ)^3467 := by
    have hnat : (5288648291 : ℕ)^4491*10000000000000^3467 ≤ 4381600926179^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288648291 10000000000 4381600926179 10000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5461146567/10000000000 : ℝ)^4491 ≤ (913521924601/2000000000000 : ℝ)^3467 := by
    have hnat : (5461146567 : ℕ)^4491*2000000000000^3467 ≤ 913521924601^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461146567 10000000000 913521924601 2000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1756392009/10000000000 : ℝ)^4491 ≤ (5253947244163/50000000000000 : ℝ)^3467 := by
    have hnat : (1756392009 : ℕ)^4491*50000000000000^3467 ≤ 5253947244163^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756392009 10000000000 5253947244163 50000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288648291/10000000000 : ℝ), (5461146567/10000000000 : ℝ), (-1756392009/10000000000 : ℝ)] ![(4381600926179/10000000000000 : ℝ), (913521924601/2000000000000 : ℝ), (5253947244163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288648291/10000000000 : ℝ)|^4491 ≤ (4381600926179/10000000000000 : ℝ)^3467
        have hw : |(5288648291/10000000000 : ℝ)|=(5288648291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5461146567/10000000000 : ℝ)|^4491 ≤ (913521924601/2000000000000 : ℝ)^3467
        have hw : |(5461146567/10000000000 : ℝ)|=(5461146567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1756392009/10000000000 : ℝ)|^4491 ≤ (5253947244163/50000000000000 : ℝ)^3467
        have hw : |(-1756392009/10000000000 : ℝ)|=(1756392009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1497_s2_7 (p : ℝ) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4274033273/10000000000 : ℝ)*x 0 + (4583085043/10000000000 : ℝ)*x 1 + (995825717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4274033273/10000000000 : ℝ)^4491 ≤ (33250913226821/100000000000000 : ℝ)^3467 := by
    have hnat : (4274033273 : ℕ)^4491*100000000000000^3467 ≤ 33250913226821^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274033273 10000000000 33250913226821 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4583085043/10000000000 : ℝ)^4491 ≤ (36398107251077/100000000000000 : ℝ)^3467 := by
    have hnat : (4583085043 : ℕ)^4491*100000000000000^3467 ≤ 36398107251077^3467*10000000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4583085043 10000000000 36398107251077 100000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995825717/2500000000 : ℝ)^4491 ≤ (6070195900421/20000000000000 : ℝ)^3467 := by
    have hnat : (995825717 : ℕ)^4491*20000000000000^3467 ≤ 6070195900421^3467*2500000000^4491 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995825717 2500000000 6070195900421 20000000000000 4491 3467 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4491/1024 : ℝ)) 4491 3467 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4274033273/10000000000 : ℝ), (4583085043/10000000000 : ℝ), (995825717/2500000000 : ℝ)] ![(33250913226821/100000000000000 : ℝ), (36398107251077/100000000000000 : ℝ), (6070195900421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4274033273/10000000000 : ℝ)|^4491 ≤ (33250913226821/100000000000000 : ℝ)^3467
        have hw : |(4274033273/10000000000 : ℝ)|=(4274033273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4583085043/10000000000 : ℝ)|^4491 ≤ (36398107251077/100000000000000 : ℝ)^3467
        have hw : |(4583085043/10000000000 : ℝ)|=(4583085043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(995825717/2500000000 : ℝ)|^4491 ≤ (6070195900421/20000000000000 : ℝ)^3467
        have hw : |(995825717/2500000000 : ℝ)|=(995825717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1497_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162181901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18499/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (163/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (5163/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2007/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18499/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (163/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18499/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (163/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18499/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (163/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18499/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (163/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18499/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (163/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18499/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (163/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (163/2000 : ℝ) ^ (4489/1024 : ℝ) ≤ (842780811007831/50000000000000000000 : ℝ) := by
    have hpowers : (163/2000 : ℝ)^4489 ≤ (842780811007831/50000000000000000000 : ℝ)^1024 := by
      have hnat : (163 : ℕ)^4489*50000000000000000000^1024 ≤ 842780811007831^1024*2000^4489 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        163 2000 842780811007831 50000000000000000000 4489 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (163/2000 : ℝ)) (X := (842780811007831/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18499/100000 : ℝ) ^ (4489/1024 : ℝ) ≤ (12256388539379139/20000000000000000000 : ℝ) := by
    have hpowers : (18499/100000 : ℝ)^4489 ≤ (12256388539379139/20000000000000000000 : ℝ)^1024 := by
      have hnat : (18499 : ℕ)^4489*20000000000000000000^1024 ≤ 12256388539379139^1024*100000^4489 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18499 100000 12256388539379139 20000000000000000000 4489 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18499/100000 : ℝ)) (X := (12256388539379139/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000842780811007831/25000000000000000000 : ℝ) ≤ (125000961234487/125000000000000 : ℝ) ^ (4489/1024 : ℝ) := by
    have hpowers : (25000842780811007831/25000000000000000000 : ℝ)^1024 ≤ (125000961234487/125000000000000 : ℝ)^4489 := by
      have hnat : (25000842780811007831 : ℕ)^1024*125000000000000^4489 ≤ 125000961234487^4489*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000842780811007831 25000000000000000000 125000961234487 125000000000000 1024 4489 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125000961234487/125000000000000 : ℝ)) (X := (25000842780811007831/25000000000000000000 : ℝ)) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100062967504318911357/100000000000000000000 : ℝ) ≤ (400057440909509/400000000000000 : ℝ) ^ (4489/1024 : ℝ) := by
    have hpowers : (100062967504318911357/100000000000000000000 : ℝ)^1024 ≤ (400057440909509/400000000000000 : ℝ)^4489 := by
      have hnat : (100062967504318911357 : ℕ)^1024*400000000000000^4489 ≤ 400057440909509^4489*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100062967504318911357 100000000000000000000 400057440909509 400000000000000 1024 4489 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400057440909509/400000000000000 : ℝ)) (X := (100062967504318911357/100000000000000000000 : ℝ)) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10012256388539379139/10000000000000000000 : ℝ) ≤ (1000279514671649/1000000000000000 : ℝ) ^ (4489/1024 : ℝ) := by
    have hpowers : (10012256388539379139/10000000000000000000 : ℝ)^1024 ≤ (1000279514671649/1000000000000000 : ℝ)^4489 := by
      have hnat : (10012256388539379139 : ℕ)^1024*1000000000000000^4489 ≤ 1000279514671649^4489*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10012256388539379139 10000000000000000000 1000279514671649 1000000000000000 1024 4489 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000279514671649/1000000000000000 : ℝ)) (X := (10012256388539379139/10000000000000000000 : ℝ)) (by norm_num) 4489 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(842780811007831/50000000000000000000 : ℝ) ≤ ((5173432105220130377/5174500000000000000 : ℝ)+2*(271824795753/206980000000000 : ℝ)*(163/2000 : ℝ))^(4489/1024 : ℝ) := by
    rw [show (5173432105220130377/5174500000000000000 : ℝ)+2*(271824795753/206980000000000 : ℝ)*(163/2000 : ℝ)=(125000961234487/125000000000000 : ℝ) by norm_num, show 1+2*(842780811007831/50000000000000000000 : ℝ)=(25000842780811007831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12256388539379139/20000000000000000000 : ℝ)+(842780811007831/50000000000000000000 : ℝ) ≤ ((5173432105220130377/5174500000000000000 : ℝ)+(271824795753/206980000000000 : ℝ)*((18499/100000 : ℝ)+(163/2000 : ℝ)))^(4489/1024 : ℝ) := by
    rw [show (5173432105220130377/5174500000000000000 : ℝ)+(271824795753/206980000000000 : ℝ)*((18499/100000 : ℝ)+(163/2000 : ℝ))=(400057440909509/400000000000000 : ℝ) by norm_num, show 1+(12256388539379139/20000000000000000000 : ℝ)+(842780811007831/50000000000000000000 : ℝ)=(100062967504318911357/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12256388539379139/20000000000000000000 : ℝ) ≤ ((5173432105220130377/5174500000000000000 : ℝ)+2*(271824795753/206980000000000 : ℝ)*(18499/100000 : ℝ))^(4489/1024 : ℝ) := by
    rw [show (5173432105220130377/5174500000000000000 : ℝ)+2*(271824795753/206980000000000 : ℝ)*(18499/100000 : ℝ)=(1000279514671649/1000000000000000 : ℝ) by norm_num, show 1+2*(12256388539379139/20000000000000000000 : ℝ)=(10012256388539379139/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5173432105220130377/5174500000000000000 : ℝ)*(X 1 0+X 2 0)+(271824795753/206980000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4489/1024 : ℝ)) (lo := (163/2000 : ℝ)) (hi := (18499/100000 : ℝ)) (c := (5173432105220130377/5174500000000000000 : ℝ)) (alpha := (271824795753/206980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5173432105220130377/5174500000000000000 : ℝ)*(X 0 1+X 2 1)+(271824795753/206980000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4489/1024 : ℝ)) (lo := (163/2000 : ℝ)) (hi := (18499/100000 : ℝ)) (c := (5173432105220130377/5174500000000000000 : ℝ)) (alpha := (271824795753/206980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5173432105220130377/5174500000000000000 : ℝ)*(X 0 2+X 1 2)+(271824795753/206980000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4489/1024 : ℝ)) (lo := (163/2000 : ℝ)) (hi := (18499/100000 : ℝ)) (c := (5173432105220130377/5174500000000000000 : ℝ)) (alpha := (271824795753/206980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1885914379/10000000000 : ℝ)*X 0 0+(5462883267/10000000000 : ℝ)*X 0 1+(519210211/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2679794789/5000000000 : ℝ)*X 1 0+(-2025436011/10000000000 : ℝ)*X 1 1+(519210149/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679794747/5000000000 : ℝ)*X 2 0+(2596050693/5000000000 : ℝ)*X 2 1+(-101271813/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4273905901/10000000000 : ℝ)*X 0 0+(248713083/625000000 : ℝ)*X 0 1+(2293472167/5000000000 : ℝ)*X 0 2+(4273905901/10000000000 : ℝ)*X 1 0+(248713083/625000000 : ℝ)*X 1 1+(2293472167/5000000000 : ℝ)*X 1 2+(4273905901/10000000000 : ℝ)*X 2 0+(248713083/625000000 : ℝ)*X 2 1+(2293472167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-942984639/5000000000 : ℝ)*X 0 0+(1298455951/2500000000 : ℝ)*X 0 1+(5461146967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322162197/2500000000 : ℝ)*X 1 0+(-1756390081/10000000000 : ℝ)*X 1 1+(1092229491/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288648291/10000000000 : ℝ)*X 2 0+(5461146567/10000000000 : ℝ)*X 2 1+(-1756392009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4274033273/10000000000 : ℝ)*X 0 0+(4583085043/10000000000 : ℝ)*X 0 1+(995825717/2500000000 : ℝ)*X 0 2+(4274033273/10000000000 : ℝ)*X 1 0+(4583085043/10000000000 : ℝ)*X 1 1+(995825717/2500000000 : ℝ)*X 1 2+(4274033273/10000000000 : ℝ)*X 2 0+(4583085043/10000000000 : ℝ)*X 2 1+(995825717/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1497_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (363969411296275190712816537/51745000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (630230551/20000000000000 : ℝ)*(base19) + (2736887877/100000000000000 : ℝ)*(base23) + (20695543/100000000000000 : ℝ)*(upper2) + (92787223/20000000000000 : ℝ)*(upper3) + (211702597/100000000000000 : ℝ)*(upper4) + (533911534836027/20000000000000 : ℝ)*(major0) + (533911534836027/20000000000000 : ℝ)*(major1) + (533911534836027/20000000000000 : ℝ)*(major2) + (369305768300863/10000000000000 : ℝ)*(sp0) + (3693085089387693/100000000000000 : ℝ)*(sp1) + (923271375913143/25000000000000 : ℝ)*(sp2) + (823004397174333/50000000000000 : ℝ)*(sp3) + (30557531819/100000000000000 : ℝ)*(sp4) + (18079007649/100000000000000 : ℝ)*(sp7) + (411506718339079/25000000000000 : ℝ)*(f.failure) + (115409007516889/3125000000000 : ℝ)*(f.sum) + (14631282841399/2587250000000000000000000000 : ℝ)*base65 + (278109882513122821/103490000000000000000000000000000 : ℝ)*base68 + (609824724501042821/103490000000000000000000000000000 : ℝ)*base70 + (340513726068437179/103490000000000000000000000000000 : ℝ)*base71 + (17543071278187/10349000000000000000000000000 : ℝ)*base73 + (145247598862427179/103490000000000000000000000000000 : ℝ)*base75 + (250726197730422821/103490000000000000000000000000000 : ℝ)*base78 + (1218880667473062821/103490000000000000000000000000000 : ℝ)*base80 + (63317760872111/10349000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (19809179/2500000000000000000000 : ℝ)*base89 + (19809179/2500000000000000000000 : ℝ)*base91 + (19809179/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (312808313601092742314488641/64681250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (399538647/50000000000000 : ℝ)*(base19) + (538288903/50000000000000 : ℝ)*(base23) + (45006819/10000000000000 : ℝ)*(lower4) + (27182143/100000000000000 : ℝ)*(lower5) + (676008063316461/25000000000000 : ℝ)*(major0) + (676008063316461/25000000000000 : ℝ)*(major1) + (676008063316461/25000000000000 : ℝ)*(major2) + (20265663549/100000000000000 : ℝ)*(sp1) + (1858937503/50000000000000 : ℝ)*(sp2) + (7446797297/100000000000000 : ℝ)*(sp3) + (3740780735630973/100000000000000 : ℝ)*(sp4) + (3740759670890131/100000000000000 : ℝ)*(sp5) + (46759699264727/1250000000000 : ℝ)*(sp6) + (416819040724591/25000000000000 : ℝ)*(sp7) + (833641804847831/50000000000000 : ℝ)*(f.failure) + (3740780735630973/100000000000000 : ℝ)*(f.sum) + (48042656961757/10349000000000000000000000000 : ℝ)*base65 + (175782695799439203/129362500000000000000000000000000 : ℝ)*base68 + (426018810404698297/129362500000000000000000000000000 : ℝ)*base69 + (979121383480576703/129362500000000000000000000000000 : ℝ)*base72 + (1070234836733/206980000000000000000000000 : ℝ)*base73 + (617502647066251703/129362500000000000000000000000000 : ℝ)*base76 + (449266551267151703/129362500000000000000000000000000 : ℝ)*base78 + (1697431096742360797/129362500000000000000000000000000 : ℝ)*base79 + (9347664170091/5174500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (47306731/5000000000000000000000 : ℝ)*base89 + (47306731/5000000000000000000000 : ℝ)*base91 + (47306731/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1497_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162181901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18499/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (163/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5163/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2007/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1497_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1497_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162181901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5163/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2007/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1497_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1497_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1497_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4489/1024 : ℝ) ≤ p) (hpb : p ≤ (4491/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162181901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5163/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2007/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1497_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
