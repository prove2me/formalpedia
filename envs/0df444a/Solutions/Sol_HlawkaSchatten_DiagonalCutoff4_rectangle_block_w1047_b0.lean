-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1047_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:52:00.863662+00:00
-- url     : https://prove2.me/submissions/9fd23cb1-1932-4005-ab89-0c0da0223503

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
theorem support_rectangle_w1047_s0_0 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-480561031/2500000000 : ℝ)*x 0 + (6076548531/10000000000 : ℝ)*x 1 + (238417133/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480561031/2500000000 : ℝ)^515 ≤ (139263944823/1250000000000 : ℝ)^387 := by
    have hnat : (480561031 : ℕ)^515*1250000000000^387 ≤ 139263944823^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480561031 2500000000 139263944823 1250000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6076548531/10000000000 : ℝ)^515 ≤ (10306985125657/20000000000000 : ℝ)^387 := by
    have hnat : (6076548531 : ℕ)^515*20000000000000^387 ≤ 10306985125657^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6076548531 10000000000 10306985125657 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238417133/500000000 : ℝ)^515 ≤ (18661979385359/50000000000000 : ℝ)^387 := by
    have hnat : (238417133 : ℕ)^515*50000000000000^387 ≤ 18661979385359^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238417133 500000000 18661979385359 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-480561031/2500000000 : ℝ), (6076548531/10000000000 : ℝ), (238417133/500000000 : ℝ)] ![(139263944823/1250000000000 : ℝ), (10306985125657/20000000000000 : ℝ), (18661979385359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-480561031/2500000000 : ℝ)|^515 ≤ (139263944823/1250000000000 : ℝ)^387
        have hw : |(-480561031/2500000000 : ℝ)|=(480561031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6076548531/10000000000 : ℝ)|^515 ≤ (10306985125657/20000000000000 : ℝ)^387
        have hw : |(6076548531/10000000000 : ℝ)|=(6076548531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(238417133/500000000 : ℝ)|^515 ≤ (18661979385359/50000000000000 : ℝ)^387
        have hw : |(238417133/500000000 : ℝ)|=(238417133/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s0_1 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5522145749/10000000000 : ℝ)*x 0 + (-2675825583/10000000000 : ℝ)*x 1 + (596042481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5522145749/10000000000 : ℝ)^515 ≤ (453743281931/1000000000000 : ℝ)^387 := by
    have hnat : (5522145749 : ℕ)^515*1000000000000^387 ≤ 453743281931^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522145749 10000000000 453743281931 1000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2675825583/10000000000 : ℝ)^515 ≤ (4325435577117/25000000000000 : ℝ)^387 := by
    have hnat : (2675825583 : ℕ)^515*25000000000000^387 ≤ 4325435577117^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675825583 10000000000 4325435577117 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (596042481/1250000000 : ℝ)^515 ≤ (37323929479881/100000000000000 : ℝ)^387 := by
    have hnat : (596042481 : ℕ)^515*100000000000000^387 ≤ 37323929479881^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596042481 1250000000 37323929479881 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5522145749/10000000000 : ℝ), (-2675825583/10000000000 : ℝ), (596042481/1250000000 : ℝ)] ![(453743281931/1000000000000 : ℝ), (4325435577117/25000000000000 : ℝ), (37323929479881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5522145749/10000000000 : ℝ)|^515 ≤ (453743281931/1000000000000 : ℝ)^387
        have hw : |(5522145749/10000000000 : ℝ)|=(5522145749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2675825583/10000000000 : ℝ)|^515 ≤ (4325435577117/25000000000000 : ℝ)^387
        have hw : |(-2675825583/10000000000 : ℝ)|=(2675825583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(596042481/1250000000 : ℝ)|^515 ≤ (37323929479881/100000000000000 : ℝ)^387
        have hw : |(596042481/1250000000 : ℝ)|=(596042481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s0_2 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2761072373/5000000000 : ℝ)*x 0 + (596042479/1250000000 : ℝ)*x 1 + (-1337913439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2761072373/5000000000 : ℝ)^515 ≤ (9074863445161/20000000000000 : ℝ)^387 := by
    have hnat : (2761072373 : ℕ)^515*20000000000000^387 ≤ 9074863445161^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761072373 5000000000 9074863445161 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (596042479/1250000000 : ℝ)^515 ≤ (37323929313219/100000000000000 : ℝ)^387 := by
    have hnat : (596042479 : ℕ)^515*100000000000000^387 ≤ 37323929313219^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596042479 1250000000 37323929313219 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1337913439/5000000000 : ℝ)^515 ≤ (3460350690273/20000000000000 : ℝ)^387 := by
    have hnat : (1337913439 : ℕ)^515*20000000000000^387 ≤ 3460350690273^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337913439 5000000000 3460350690273 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2761072373/5000000000 : ℝ), (596042479/1250000000 : ℝ), (-1337913439/5000000000 : ℝ)] ![(9074863445161/20000000000000 : ℝ), (37323929313219/100000000000000 : ℝ), (3460350690273/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2761072373/5000000000 : ℝ)|^515 ≤ (9074863445161/20000000000000 : ℝ)^387
        have hw : |(2761072373/5000000000 : ℝ)|=(2761072373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(596042479/1250000000 : ℝ)|^515 ≤ (37323929313219/100000000000000 : ℝ)^387
        have hw : |(596042479/1250000000 : ℝ)|=(596042479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1337913439/5000000000 : ℝ)|^515 ≤ (3460350690273/20000000000000 : ℝ)^387
        have hw : |(-1337913439/5000000000 : ℝ)|=(1337913439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s0_3 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4208783341/10000000000 : ℝ)*x 0 + (625179827/2000000000 : ℝ)*x 1 + (5680138967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208783341/10000000000 : ℝ)^515 ≤ (15805804371649/50000000000000 : ℝ)^387 := by
    have hnat : (4208783341 : ℕ)^515*50000000000000^387 ≤ 15805804371649^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208783341 10000000000 15805804371649 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625179827/2000000000 : ℝ)^515 ≤ (5319591254277/25000000000000 : ℝ)^387 := by
    have hnat : (625179827 : ℕ)^515*25000000000000^387 ≤ 5319591254277^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625179827 2000000000 5319591254277 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5680138967/10000000000 : ℝ)^515 ≤ (23555013117169/50000000000000 : ℝ)^387 := by
    have hnat : (5680138967 : ℕ)^515*50000000000000^387 ≤ 23555013117169^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5680138967 10000000000 23555013117169 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208783341/10000000000 : ℝ), (625179827/2000000000 : ℝ), (5680138967/10000000000 : ℝ)] ![(15805804371649/50000000000000 : ℝ), (5319591254277/25000000000000 : ℝ), (23555013117169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208783341/10000000000 : ℝ)|^515 ≤ (15805804371649/50000000000000 : ℝ)^387
        have hw : |(4208783341/10000000000 : ℝ)|=(4208783341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625179827/2000000000 : ℝ)|^515 ≤ (5319591254277/25000000000000 : ℝ)^387
        have hw : |(625179827/2000000000 : ℝ)|=(625179827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5680138967/10000000000 : ℝ)|^515 ≤ (23555013117169/50000000000000 : ℝ)^387
        have hw : |(5680138967/10000000000 : ℝ)|=(5680138967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s0_4 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-192767717/1000000000 : ℝ)*x 0 + (2401064101/5000000000 : ℝ)*x 1 + (6041581873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (192767717/1000000000 : ℝ)^515 ≤ (2236607915099/20000000000000 : ℝ)^387 := by
    have hnat : (192767717 : ℕ)^515*20000000000000^387 ≤ 2236607915099^387*1000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192767717 1000000000 2236607915099 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2401064101/5000000000 : ℝ)^515 ≤ (2354768329957/6250000000000 : ℝ)^387 := by
    have hnat : (2401064101 : ℕ)^515*6250000000000^387 ≤ 2354768329957^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401064101 5000000000 2354768329957 6250000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6041581873/10000000000 : ℝ)^515 ≤ (51140667135039/100000000000000 : ℝ)^387 := by
    have hnat : (6041581873 : ℕ)^515*100000000000000^387 ≤ 51140667135039^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6041581873 10000000000 51140667135039 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-192767717/1000000000 : ℝ), (2401064101/5000000000 : ℝ), (6041581873/10000000000 : ℝ)] ![(2236607915099/20000000000000 : ℝ), (2354768329957/6250000000000 : ℝ), (51140667135039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-192767717/1000000000 : ℝ)|^515 ≤ (2236607915099/20000000000000 : ℝ)^387
        have hw : |(-192767717/1000000000 : ℝ)|=(192767717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2401064101/5000000000 : ℝ)|^515 ≤ (2354768329957/6250000000000 : ℝ)^387
        have hw : |(2401064101/5000000000 : ℝ)|=(2401064101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6041581873/10000000000 : ℝ)|^515 ≤ (51140667135039/100000000000000 : ℝ)^387
        have hw : |(6041581873/10000000000 : ℝ)|=(6041581873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s0_5 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5167181283/10000000000 : ℝ)*x 0 + (-1402586921/10000000000 : ℝ)*x 1 + (6041582147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167181283/10000000000 : ℝ)^515 ≤ (5191855030623/12500000000000 : ℝ)^387 := by
    have hnat : (5167181283 : ℕ)^515*12500000000000^387 ≤ 5191855030623^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167181283 10000000000 5191855030623 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1402586921/10000000000 : ℝ)^515 ≤ (3662244762433/50000000000000 : ℝ)^387 := by
    have hnat : (1402586921 : ℕ)^515*50000000000000^387 ≤ 3662244762433^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402586921 10000000000 3662244762433 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6041582147/10000000000 : ℝ)^515 ≤ (51140670221513/100000000000000 : ℝ)^387 := by
    have hnat : (6041582147 : ℕ)^515*100000000000000^387 ≤ 51140670221513^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6041582147 10000000000 51140670221513 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167181283/10000000000 : ℝ), (-1402586921/10000000000 : ℝ), (6041582147/10000000000 : ℝ)] ![(5191855030623/12500000000000 : ℝ), (3662244762433/50000000000000 : ℝ), (51140670221513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167181283/10000000000 : ℝ)|^515 ≤ (5191855030623/12500000000000 : ℝ)^387
        have hw : |(5167181283/10000000000 : ℝ)|=(5167181283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1402586921/10000000000 : ℝ)|^515 ≤ (3662244762433/50000000000000 : ℝ)^387
        have hw : |(-1402586921/10000000000 : ℝ)|=(1402586921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6041582147/10000000000 : ℝ)|^515 ≤ (51140670221513/100000000000000 : ℝ)^387
        have hw : |(6041582147/10000000000 : ℝ)|=(6041582147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s0_6 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1033435993/2000000000 : ℝ)*x 0 + (6041583323/10000000000 : ℝ)*x 1 + (-1402587043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033435993/2000000000 : ℝ)^515 ≤ (20767413073281/50000000000000 : ℝ)^387 := by
    have hnat : (1033435993 : ℕ)^515*50000000000000^387 ≤ 20767413073281^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033435993 2000000000 20767413073281 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6041583323/10000000000 : ℝ)^515 ≤ (6392585433571/12500000000000 : ℝ)^387 := by
    have hnat : (6041583323 : ℕ)^515*12500000000000^387 ≤ 6392585433571^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6041583323 10000000000 6392585433571 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1402587043/10000000000 : ℝ)^515 ≤ (7324490372687/100000000000000 : ℝ)^387 := by
    have hnat : (1402587043 : ℕ)^515*100000000000000^387 ≤ 7324490372687^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402587043 10000000000 7324490372687 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033435993/2000000000 : ℝ), (6041583323/10000000000 : ℝ), (-1402587043/10000000000 : ℝ)] ![(20767413073281/50000000000000 : ℝ), (6392585433571/12500000000000 : ℝ), (7324490372687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033435993/2000000000 : ℝ)|^515 ≤ (20767413073281/50000000000000 : ℝ)^387
        have hw : |(1033435993/2000000000 : ℝ)|=(1033435993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6041583323/10000000000 : ℝ)|^515 ≤ (6392585433571/12500000000000 : ℝ)^387
        have hw : |(6041583323/10000000000 : ℝ)|=(6041583323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1402587043/10000000000 : ℝ)|^515 ≤ (7324490372687/100000000000000 : ℝ)^387
        have hw : |(-1402587043/10000000000 : ℝ)|=(1402587043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s0_7 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4219389637/10000000000 : ℝ)*x 0 + (701771127/1250000000 : ℝ)*x 1 + (3194169281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4219389637/10000000000 : ℝ)^515 ≤ (31717663679893/100000000000000 : ℝ)^387 := by
    have hnat : (4219389637 : ℕ)^515*100000000000000^387 ≤ 31717663679893^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219389637 10000000000 31717663679893 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (701771127/1250000000 : ℝ)^515 ≤ (9276663731081/20000000000000 : ℝ)^387 := by
    have hnat : (701771127 : ℕ)^515*20000000000000^387 ≤ 9276663731081^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701771127 1250000000 9276663731081 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3194169281/10000000000 : ℝ)^515 ≤ (21899017656729/100000000000000 : ℝ)^387 := by
    have hnat : (3194169281 : ℕ)^515*100000000000000^387 ≤ 21899017656729^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3194169281 10000000000 21899017656729 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4219389637/10000000000 : ℝ), (701771127/1250000000 : ℝ), (3194169281/10000000000 : ℝ)] ![(31717663679893/100000000000000 : ℝ), (9276663731081/20000000000000 : ℝ), (21899017656729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4219389637/10000000000 : ℝ)|^515 ≤ (31717663679893/100000000000000 : ℝ)^387
        have hw : |(4219389637/10000000000 : ℝ)|=(4219389637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(701771127/1250000000 : ℝ)|^515 ≤ (9276663731081/20000000000000 : ℝ)^387
        have hw : |(701771127/1250000000 : ℝ)|=(701771127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3194169281/10000000000 : ℝ)|^515 ≤ (21899017656729/100000000000000 : ℝ)^387
        have hw : |(3194169281/10000000000 : ℝ)|=(3194169281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1047_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28183/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
  have base61 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [sign5]
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
  have hpowlo : (0 : ℝ) ^ (8239/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8239 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8239*1^2048 ≤ 0^2048*1^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8239/2048 : ℝ) ≤ (626682491925313153/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8239 ≤ (626682491925313153/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8239*25000000000000000000^2048 ≤ 626682491925313153^2048*5^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 626682491925313153 25000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (626682491925313153/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8239 := by
      have hnat : (1 : ℕ)^2048*1^8239 ≤ 1^8239*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25626682491925313153/25000000000000000000 : ℝ) ≤ (5030866173326129/5000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (25626682491925313153/25000000000000000000 : ℝ)^2048 ≤ (5030866173326129/5000000000000000 : ℝ)^8239 := by
      have hnat : (25626682491925313153 : ℕ)^2048*5000000000000000^8239 ≤ 5030866173326129^8239*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25626682491925313153 25000000000000000000 5030866173326129 5000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030866173326129/5000000000000000 : ℝ)) (X := (25626682491925313153/25000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (13126682491925313153/12500000000000000000 : ℝ) ≤ (2530866173326129/2500000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (13126682491925313153/12500000000000000000 : ℝ)^2048 ≤ (2530866173326129/2500000000000000 : ℝ)^8239 := by
      have hnat : (13126682491925313153 : ℕ)^2048*2500000000000000^8239 ≤ 2530866173326129^8239*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13126682491925313153 12500000000000000000 2530866173326129 2500000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2530866173326129/2500000000000000 : ℝ)) (X := (13126682491925313153/12500000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30866173326129/2000000000000000 : ℝ)*(0 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(30866173326129/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(626682491925313153/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30866173326129/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8239/2048 : ℝ) := by
    rw [show (1 : ℝ)+(30866173326129/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5030866173326129/5000000000000000 : ℝ) by norm_num, show 1+(626682491925313153/25000000000000000000 : ℝ)+(0 : ℝ)=(25626682491925313153/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(626682491925313153/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30866173326129/2000000000000000 : ℝ)*(2/5 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(30866173326129/2000000000000000 : ℝ)*(2/5 : ℝ)=(2530866173326129/2500000000000000 : ℝ) by norm_num, show 1+2*(626682491925313153/25000000000000000000 : ℝ)=(13126682491925313153/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30866173326129/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30866173326129/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30866173326129/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30866173326129/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30866173326129/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30866173326129/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-480561031/2500000000 : ℝ)*X 0 0+(6076548531/10000000000 : ℝ)*X 0 1+(238417133/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5522145749/10000000000 : ℝ)*X 1 0+(-2675825583/10000000000 : ℝ)*X 1 1+(596042481/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2761072373/5000000000 : ℝ)*X 2 0+(596042479/1250000000 : ℝ)*X 2 1+(-1337913439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4208783341/10000000000 : ℝ)*X 0 0+(625179827/2000000000 : ℝ)*X 0 1+(5680138967/10000000000 : ℝ)*X 0 2+(4208783341/10000000000 : ℝ)*X 1 0+(625179827/2000000000 : ℝ)*X 1 1+(5680138967/10000000000 : ℝ)*X 1 2+(4208783341/10000000000 : ℝ)*X 2 0+(625179827/2000000000 : ℝ)*X 2 1+(5680138967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-192767717/1000000000 : ℝ)*X 0 0+(2401064101/5000000000 : ℝ)*X 0 1+(6041581873/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5167181283/10000000000 : ℝ)*X 1 0+(-1402586921/10000000000 : ℝ)*X 1 1+(6041582147/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1033435993/2000000000 : ℝ)*X 2 0+(6041583323/10000000000 : ℝ)*X 2 1+(-1402587043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4219389637/10000000000 : ℝ)*X 0 0+(701771127/1250000000 : ℝ)*X 0 1+(3194169281/10000000000 : ℝ)*X 0 2+(4219389637/10000000000 : ℝ)*X 1 0+(701771127/1250000000 : ℝ)*X 1 1+(3194169281/10000000000 : ℝ)*X 1 2+(4219389637/10000000000 : ℝ)*X 2 0+(701771127/1250000000 : ℝ)*X 2 1+(3194169281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46924982888339537892273/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2051319/20000000000000 : ℝ)*(base1) + (1446441/3125000000000 : ℝ)*(base16) + (255802483/20000000000000 : ℝ)*(base19) + (47458267/4000000000000 : ℝ)*(base23) + (117431147/100000000000000 : ℝ)*(base61) + (144490441340679/25000000000000 : ℝ)*(major0) + (144490441340679/25000000000000 : ℝ)*(major1) + (144490441340679/25000000000000 : ℝ)*(major2) + (191102386785441/25000000000000 : ℝ)*(sp0) + (76441156697683/10000000000000 : ℝ)*(sp1) + (382205852909341/50000000000000 : ℝ)*(sp2) + (195754045586413/50000000000000 : ℝ)*(sp3) + (3355390189/100000000000000 : ℝ)*(sp4) + (1884287/78125000000 : ℝ)*(sp7) + (391510513316781/100000000000000 : ℝ)*(f.failure) + (382206446137679/50000000000000 : ℝ)*(f.sum) + (1772041698409/25000000000000000000000000000 : ℝ)*base66 + (282749645298409/50000000000000000000000000000 : ℝ)*base68 + (191484295648409/50000000000000000000000000000 : ℝ)*base70 + (163996678501591/50000000000000000000000000000 : ℝ)*base71 + (97922073198409/25000000000000000000000000000 : ℝ)*base74 + (192094424201591/50000000000000000000000000000 : ℝ)*base75 + (70549223401591/50000000000000000000000000000 : ℝ)*base77 + (169431226601591/50000000000000000000000000000 : ℝ)*base79 + (75608641348409/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (22796961/5000000000000000000000 : ℝ)*base89 + (22796961/5000000000000000000000 : ℝ)*base91 + (22796961/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3024891846765192376407/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78845231/25000000000000 : ℝ)*(base19) + (376417601/100000000000000 : ℝ)*(base23) + (130098369/50000000000000 : ℝ)*(base39) + (50032097/50000000000000 : ℝ)*(base45) + (20513309/100000000000000 : ℝ)*(upper2) + (24921949/25000000000000 : ℝ)*(upper5) + (305006799171711/50000000000000 : ℝ)*(major0) + (305006799171711/50000000000000 : ℝ)*(major1) + (152503334536671/25000000000000 : ℝ)*(major2) + (11506843/3125000000000 : ℝ)*(sp1) + (201701126179051/25000000000000 : ℝ)*(sp4) + (161360764223261/20000000000000 : ℝ)*(sp5) + (806804388495341/100000000000000 : ℝ)*(sp6) + (103305595339757/25000000000000 : ℝ)*(sp7) + (103305595339757/25000000000000 : ℝ)*(f.failure) + (403402382456471/50000000000000 : ℝ)*(f.sum) + (199295555710163/100000000000000000000000000000 : ℝ)*base66 + (511706110176559/50000000000000000000000000000 : ℝ)*base67 + (714300177936719/100000000000000000000000000000 : ℝ)*base69 + (66856934226559/50000000000000000000000000000 : ℝ)*base71 + (711700806389837/100000000000000000000000000000 : ℝ)*base73 + (228960938836719/100000000000000000000000000000 : ℝ)*base75 + (127775483836719/100000000000000000000000000000 : ℝ)*base77 + (829011614836719/100000000000000000000000000000 : ℝ)*base79 + (314981463686719/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (10722783/1250000000000000000000 : ℝ)*base90 + (10722783/1250000000000000000000 : ℝ)*base92 + (10722783/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1047_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28183/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1047_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1047_s1_0 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1066870559/5000000000 : ℝ)*x 0 + (143191691/250000000 : ℝ)*x 1 + (4981763697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066870559/5000000000 : ℝ)^515 ≤ (3200337602687/25000000000000 : ℝ)^387 := by
    have hnat : (1066870559 : ℕ)^515*25000000000000^387 ≤ 3200337602687^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066870559 5000000000 3200337602687 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (143191691/250000000 : ℝ)^515 ≤ (4763532426479/10000000000000 : ℝ)^387 := by
    have hnat : (143191691 : ℕ)^515*10000000000000^387 ≤ 4763532426479^387*250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143191691 250000000 4763532426479 10000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4981763697/10000000000 : ℝ)^515 ≤ (39563325318037/100000000000000 : ℝ)^387 := by
    have hnat : (4981763697 : ℕ)^515*100000000000000^387 ≤ 39563325318037^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4981763697 10000000000 39563325318037 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1066870559/5000000000 : ℝ), (143191691/250000000 : ℝ), (4981763697/10000000000 : ℝ)] ![(3200337602687/25000000000000 : ℝ), (4763532426479/10000000000000 : ℝ), (39563325318037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1066870559/5000000000 : ℝ)|^515 ≤ (3200337602687/25000000000000 : ℝ)^387
        have hw : |(-1066870559/5000000000 : ℝ)|=(1066870559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(143191691/250000000 : ℝ)|^515 ≤ (4763532426479/10000000000000 : ℝ)^387
        have hw : |(143191691/250000000 : ℝ)|=(143191691/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4981763697/10000000000 : ℝ)|^515 ≤ (39563325318037/100000000000000 : ℝ)^387
        have hw : |(4981763697/10000000000 : ℝ)|=(4981763697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s1_1 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1356089913/2500000000 : ℝ)*x 0 + (-634571119/2500000000 : ℝ)*x 1 + (4981764021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1356089913/2500000000 : ℝ)^515 ≤ (44308230592657/100000000000000 : ℝ)^387 := by
    have hnat : (1356089913 : ℕ)^515*100000000000000^387 ≤ 44308230592657^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356089913 2500000000 44308230592657 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (634571119/2500000000 : ℝ)^515 ≤ (8064220325587/50000000000000 : ℝ)^387 := by
    have hnat : (634571119 : ℕ)^515*50000000000000^387 ≤ 8064220325587^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634571119 2500000000 8064220325587 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4981764021/10000000000 : ℝ)^515 ≤ (9890832185543/25000000000000 : ℝ)^387 := by
    have hnat : (4981764021 : ℕ)^515*25000000000000^387 ≤ 9890832185543^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4981764021 10000000000 9890832185543 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1356089913/2500000000 : ℝ), (-634571119/2500000000 : ℝ), (4981764021/10000000000 : ℝ)] ![(44308230592657/100000000000000 : ℝ), (8064220325587/50000000000000 : ℝ), (9890832185543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1356089913/2500000000 : ℝ)|^515 ≤ (44308230592657/100000000000000 : ℝ)^387
        have hw : |(1356089913/2500000000 : ℝ)|=(1356089913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-634571119/2500000000 : ℝ)|^515 ≤ (8064220325587/50000000000000 : ℝ)^387
        have hw : |(-634571119/2500000000 : ℝ)|=(634571119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4981764021/10000000000 : ℝ)|^515 ≤ (9890832185543/25000000000000 : ℝ)^387
        have hw : |(4981764021/10000000000 : ℝ)|=(4981764021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s1_2 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5424360071/10000000000 : ℝ)*x 0 + (1245440877/2500000000 : ℝ)*x 1 + (-2538284579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5424360071/10000000000 : ℝ)^515 ≤ (8861647029443/20000000000000 : ℝ)^387 := by
    have hnat : (5424360071 : ℕ)^515*20000000000000^387 ≤ 8861647029443^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424360071 10000000000 8861647029443 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1245440877/2500000000 : ℝ)^515 ≤ (2472707707539/6250000000000 : ℝ)^387 := by
    have hnat : (1245440877 : ℕ)^515*6250000000000^387 ≤ 2472707707539^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245440877 2500000000 2472707707539 6250000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538284579/10000000000 : ℝ)^515 ≤ (4032110380527/25000000000000 : ℝ)^387 := by
    have hnat : (2538284579 : ℕ)^515*25000000000000^387 ≤ 4032110380527^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538284579 10000000000 4032110380527 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5424360071/10000000000 : ℝ), (1245440877/2500000000 : ℝ), (-2538284579/10000000000 : ℝ)] ![(8861647029443/20000000000000 : ℝ), (2472707707539/6250000000000 : ℝ), (4032110380527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5424360071/10000000000 : ℝ)|^515 ≤ (8861647029443/20000000000000 : ℝ)^387
        have hw : |(5424360071/10000000000 : ℝ)|=(5424360071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1245440877/2500000000 : ℝ)|^515 ≤ (2472707707539/6250000000000 : ℝ)^387
        have hw : |(1245440877/2500000000 : ℝ)|=(1245440877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2538284579/10000000000 : ℝ)|^515 ≤ (4032110380527/25000000000000 : ℝ)^387
        have hw : |(-2538284579/10000000000 : ℝ)|=(2538284579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s1_3 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4325373567/10000000000 : ℝ)*x 0 + (146355099/400000000 : ℝ)*x 1 + (5115232149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325373567/10000000000 : ℝ)^515 ≤ (8195560839537/25000000000000 : ℝ)^387 := by
    have hnat : (4325373567 : ℕ)^515*25000000000000^387 ≤ 8195560839537^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325373567 10000000000 8195560839537 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146355099/400000000 : ℝ)^515 ≤ (5247536294691/20000000000000 : ℝ)^387 := by
    have hnat : (146355099 : ℕ)^515*20000000000000^387 ≤ 5247536294691^387*400000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146355099 400000000 5247536294691 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5115232149/10000000000 : ℝ)^515 ≤ (40980075154517/100000000000000 : ℝ)^387 := by
    have hnat : (5115232149 : ℕ)^515*100000000000000^387 ≤ 40980075154517^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5115232149 10000000000 40980075154517 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325373567/10000000000 : ℝ), (146355099/400000000 : ℝ), (5115232149/10000000000 : ℝ)] ![(8195560839537/25000000000000 : ℝ), (5247536294691/20000000000000 : ℝ), (40980075154517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325373567/10000000000 : ℝ)|^515 ≤ (8195560839537/25000000000000 : ℝ)^387
        have hw : |(4325373567/10000000000 : ℝ)|=(4325373567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(146355099/400000000 : ℝ)|^515 ≤ (5247536294691/20000000000000 : ℝ)^387
        have hw : |(146355099/400000000 : ℝ)|=(146355099/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5115232149/10000000000 : ℝ)|^515 ≤ (40980075154517/100000000000000 : ℝ)^387
        have hw : |(5115232149/10000000000 : ℝ)|=(5115232149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s1_4 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134693349/10000000000 : ℝ)*x 0 + (39002507/78125000 : ℝ)*x 1 + (2858446353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134693349/10000000000 : ℝ)^515 ≤ (12808953405431/100000000000000 : ℝ)^387 := by
    have hnat : (2134693349 : ℕ)^515*100000000000000^387 ≤ 12808953405431^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134693349 10000000000 12808953405431 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39002507/78125000 : ℝ)^515 ≤ (19837468125511/50000000000000 : ℝ)^387 := by
    have hnat : (39002507 : ℕ)^515*50000000000000^387 ≤ 19837468125511^387*78125000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39002507 78125000 19837468125511 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2858446353/5000000000 : ℝ)^515 ≤ (23758055166619/50000000000000 : ℝ)^387 := by
    have hnat : (2858446353 : ℕ)^515*50000000000000^387 ≤ 23758055166619^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858446353 5000000000 23758055166619 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134693349/10000000000 : ℝ), (39002507/78125000 : ℝ), (2858446353/5000000000 : ℝ)] ![(12808953405431/100000000000000 : ℝ), (19837468125511/50000000000000 : ℝ), (23758055166619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134693349/10000000000 : ℝ)|^515 ≤ (12808953405431/100000000000000 : ℝ)^387
        have hw : |(-2134693349/10000000000 : ℝ)|=(2134693349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(39002507/78125000 : ℝ)|^515 ≤ (19837468125511/50000000000000 : ℝ)^387
        have hw : |(39002507/78125000 : ℝ)|=(39002507/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2858446353/5000000000 : ℝ)|^515 ≤ (23758055166619/50000000000000 : ℝ)^387
        have hw : |(2858446353/5000000000 : ℝ)|=(2858446353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s1_5 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1308514651/2500000000 : ℝ)*x 0 + (-1803154107/10000000000 : ℝ)*x 1 + (357305873/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1308514651/2500000000 : ℝ)^515 ≤ (21125871197347/50000000000000 : ℝ)^387 := by
    have hnat : (1308514651 : ℕ)^515*50000000000000^387 ≤ 21125871197347^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308514651 2500000000 21125871197347 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1803154107/10000000000 : ℝ)^515 ≤ (5116066653379/50000000000000 : ℝ)^387 := by
    have hnat : (1803154107 : ℕ)^515*50000000000000^387 ≤ 5116066653379^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803154107 10000000000 5116066653379 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (357305873/625000000 : ℝ)^515 ≤ (9503224858333/20000000000000 : ℝ)^387 := by
    have hnat : (357305873 : ℕ)^515*20000000000000^387 ≤ 9503224858333^387*625000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357305873 625000000 9503224858333 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1308514651/2500000000 : ℝ), (-1803154107/10000000000 : ℝ), (357305873/625000000 : ℝ)] ![(21125871197347/50000000000000 : ℝ), (5116066653379/50000000000000 : ℝ), (9503224858333/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1308514651/2500000000 : ℝ)|^515 ≤ (21125871197347/50000000000000 : ℝ)^387
        have hw : |(1308514651/2500000000 : ℝ)|=(1308514651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1803154107/10000000000 : ℝ)|^515 ≤ (5116066653379/50000000000000 : ℝ)^387
        have hw : |(-1803154107/10000000000 : ℝ)|=(1803154107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(357305873/625000000 : ℝ)|^515 ≤ (9503224858333/20000000000000 : ℝ)^387
        have hw : |(357305873/625000000 : ℝ)|=(357305873/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s1_6 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5234056691/10000000000 : ℝ)*x 0 + (1429224017/2500000000 : ℝ)*x 1 + (-225394219/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5234056691/10000000000 : ℝ)^515 ≤ (42251721844437/100000000000000 : ℝ)^387 := by
    have hnat : (5234056691 : ℕ)^515*100000000000000^387 ≤ 42251721844437^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234056691 10000000000 42251721844437 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1429224017/2500000000 : ℝ)^515 ≤ (11879036879711/25000000000000 : ℝ)^387 := by
    have hnat : (1429224017 : ℕ)^515*25000000000000^387 ≤ 11879036879711^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429224017 2500000000 11879036879711 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225394219/1250000000 : ℝ)^515 ≤ (5116065312999/50000000000000 : ℝ)^387 := by
    have hnat : (225394219 : ℕ)^515*50000000000000^387 ≤ 5116065312999^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225394219 1250000000 5116065312999 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5234056691/10000000000 : ℝ), (1429224017/2500000000 : ℝ), (-225394219/1250000000 : ℝ)] ![(42251721844437/100000000000000 : ℝ), (11879036879711/25000000000000 : ℝ), (5116065312999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5234056691/10000000000 : ℝ)|^515 ≤ (42251721844437/100000000000000 : ℝ)^387
        have hw : |(5234056691/10000000000 : ℝ)|=(5234056691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1429224017/2500000000 : ℝ)|^515 ≤ (11879036879711/25000000000000 : ℝ)^387
        have hw : |(1429224017/2500000000 : ℝ)|=(1429224017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225394219/1250000000 : ℝ)|^515 ≤ (5116065312999/50000000000000 : ℝ)^387
        have hw : |(-225394219/1250000000 : ℝ)|=(225394219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s1_7 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4327229549/10000000000 : ℝ)*x 0 + (5094616157/10000000000 : ℝ)*x 1 + (3679912521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327229549/10000000000 : ℝ)^515 ≤ (32800963790987/100000000000000 : ℝ)^387 := by
    have hnat : (4327229549 : ℕ)^515*100000000000000^387 ≤ 32800963790987^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327229549 10000000000 32800963790987 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5094616157/10000000000 : ℝ)^515 ≤ (40760431792199/100000000000000 : ℝ)^387 := by
    have hnat : (5094616157 : ℕ)^515*100000000000000^387 ≤ 40760431792199^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5094616157 10000000000 40760431792199 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3679912521/10000000000 : ℝ)^515 ≤ (26438604401691/100000000000000 : ℝ)^387 := by
    have hnat : (3679912521 : ℕ)^515*100000000000000^387 ≤ 26438604401691^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3679912521 10000000000 26438604401691 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327229549/10000000000 : ℝ), (5094616157/10000000000 : ℝ), (3679912521/10000000000 : ℝ)] ![(32800963790987/100000000000000 : ℝ), (40760431792199/100000000000000 : ℝ), (26438604401691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327229549/10000000000 : ℝ)|^515 ≤ (32800963790987/100000000000000 : ℝ)^387
        have hw : |(4327229549/10000000000 : ℝ)|=(4327229549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5094616157/10000000000 : ℝ)|^515 ≤ (40760431792199/100000000000000 : ℝ)^387
        have hw : |(5094616157/10000000000 : ℝ)|=(5094616157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3679912521/10000000000 : ℝ)|^515 ≤ (26438604401691/100000000000000 : ℝ)^387
        have hw : |(3679912521/10000000000 : ℝ)|=(3679912521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1047_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28183/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5101/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10441/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28183/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28183/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28183/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28183/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28183/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28183/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1/6250 : ℝ) ^ (8239/2048 : ℝ) ≤ (26813/50000000000000000000 : ℝ) := by
    have hpowers : (1/6250 : ℝ)^8239 ≤ (26813/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1 : ℕ)^8239*50000000000000000000^2048 ≤ 26813^2048*6250^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 6250 26813 50000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1/6250 : ℝ)) (X := (26813/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (28183/100000 : ℝ) ^ (8239/2048 : ℝ) ≤ (612810952975848993/100000000000000000000 : ℝ) := by
    have hpowers : (28183/100000 : ℝ)^8239 ≤ (612810952975848993/100000000000000000000 : ℝ)^2048 := by
      have hnat : (28183 : ℕ)^8239*100000000000000000000^2048 ≤ 612810952975848993^2048*100000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28183 100000 612810952975848993 100000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28183/100000 : ℝ)) (X := (612810952975848993/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000000000026813/25000000000000000000 : ℝ) ≤ (10000000000000003/10000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (25000000000000026813/25000000000000000000 : ℝ)^2048 ≤ (10000000000000003/10000000000000000 : ℝ)^8239 := by
      have hnat : (25000000000000026813 : ℕ)^2048*10000000000000000^8239 ≤ 10000000000000003^8239*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000000000026813 25000000000000000000 10000000000000003 10000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000000003/10000000000000000 : ℝ)) (X := (25000000000000026813/25000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100612810952975902619/100000000000000000000 : ℝ) ≤ (5007598965383459/5000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (100612810952975902619/100000000000000000000 : ℝ)^2048 ≤ (5007598965383459/5000000000000000 : ℝ)^8239 := by
      have hnat : (100612810952975902619 : ℕ)^2048*5000000000000000^8239 ≤ 5007598965383459^8239*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100612810952975902619 100000000000000000000 5007598965383459 5000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007598965383459/5000000000000000 : ℝ)) (X := (100612810952975902619/100000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50612810952975848993/50000000000000000000 : ℝ) ≤ (10030395861533833/10000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (50612810952975848993/50000000000000000000 : ℝ)^2048 ≤ (10030395861533833/10000000000000000 : ℝ)^8239 := by
      have hnat : (50612810952975848993 : ℕ)^2048*10000000000000000^8239 ≤ 10030395861533833^8239*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50612810952975848993 50000000000000000000 10030395861533833 10000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030395861533833/10000000000000000 : ℝ)) (X := (50612810952975848993/50000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(26813/50000000000000000000 : ℝ) ≤ ((93889837888738514407/93890000000000000000 : ℝ)+2*(1013195384461/187780000000000 : ℝ)*(1/6250 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (93889837888738514407/93890000000000000000 : ℝ)+2*(1013195384461/187780000000000 : ℝ)*(1/6250 : ℝ)=(10000000000000003/10000000000000000 : ℝ) by norm_num, show 1+2*(26813/50000000000000000000 : ℝ)=(25000000000000026813/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(612810952975848993/100000000000000000000 : ℝ)+(26813/50000000000000000000 : ℝ) ≤ ((93889837888738514407/93890000000000000000 : ℝ)+(1013195384461/187780000000000 : ℝ)*((28183/100000 : ℝ)+(1/6250 : ℝ)))^(8239/2048 : ℝ) := by
    rw [show (93889837888738514407/93890000000000000000 : ℝ)+(1013195384461/187780000000000 : ℝ)*((28183/100000 : ℝ)+(1/6250 : ℝ))=(5007598965383459/5000000000000000 : ℝ) by norm_num, show 1+(612810952975848993/100000000000000000000 : ℝ)+(26813/50000000000000000000 : ℝ)=(100612810952975902619/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(612810952975848993/100000000000000000000 : ℝ) ≤ ((93889837888738514407/93890000000000000000 : ℝ)+2*(1013195384461/187780000000000 : ℝ)*(28183/100000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (93889837888738514407/93890000000000000000 : ℝ)+2*(1013195384461/187780000000000 : ℝ)*(28183/100000 : ℝ)=(10030395861533833/10000000000000000 : ℝ) by norm_num, show 1+2*(612810952975848993/100000000000000000000 : ℝ)=(50612810952975848993/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (93889837888738514407/93890000000000000000 : ℝ)*(X 1 0+X 2 0)+(1013195384461/187780000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (1/6250 : ℝ)) (hi := (28183/100000 : ℝ)) (c := (93889837888738514407/93890000000000000000 : ℝ)) (alpha := (1013195384461/187780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (93889837888738514407/93890000000000000000 : ℝ)*(X 0 1+X 2 1)+(1013195384461/187780000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (1/6250 : ℝ)) (hi := (28183/100000 : ℝ)) (c := (93889837888738514407/93890000000000000000 : ℝ)) (alpha := (1013195384461/187780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (93889837888738514407/93890000000000000000 : ℝ)*(X 0 2+X 1 2)+(1013195384461/187780000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (1/6250 : ℝ)) (hi := (28183/100000 : ℝ)) (c := (93889837888738514407/93890000000000000000 : ℝ)) (alpha := (1013195384461/187780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1066870559/5000000000 : ℝ)*X 0 0+(143191691/250000000 : ℝ)*X 0 1+(4981763697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1356089913/2500000000 : ℝ)*X 1 0+(-634571119/2500000000 : ℝ)*X 1 1+(4981764021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5424360071/10000000000 : ℝ)*X 2 0+(1245440877/2500000000 : ℝ)*X 2 1+(-2538284579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4325373567/10000000000 : ℝ)*X 0 0+(146355099/400000000 : ℝ)*X 0 1+(5115232149/10000000000 : ℝ)*X 0 2+(4325373567/10000000000 : ℝ)*X 1 0+(146355099/400000000 : ℝ)*X 1 1+(5115232149/10000000000 : ℝ)*X 1 2+(4325373567/10000000000 : ℝ)*X 2 0+(146355099/400000000 : ℝ)*X 2 1+(5115232149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2134693349/10000000000 : ℝ)*X 0 0+(39002507/78125000 : ℝ)*X 0 1+(2858446353/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1308514651/2500000000 : ℝ)*X 1 0+(-1803154107/10000000000 : ℝ)*X 1 1+(357305873/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5234056691/10000000000 : ℝ)*X 2 0+(1429224017/2500000000 : ℝ)*X 2 1+(-225394219/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4327229549/10000000000 : ℝ)*X 0 0+(5094616157/10000000000 : ℝ)*X 0 1+(3679912521/10000000000 : ℝ)*X 0 2+(4327229549/10000000000 : ℝ)*X 1 0+(5094616157/10000000000 : ℝ)*X 1 1+(3679912521/10000000000 : ℝ)*X 1 2+(4327229549/10000000000 : ℝ)*X 2 0+(5094616157/10000000000 : ℝ)*X 2 1+(3679912521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3607127499653813934002630979/938900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15889843/20000000000000 : ℝ)*(base1) + (863683897/100000000000000 : ℝ)*(base19) + (967242271/100000000000000 : ℝ)*(base23) + (47878649/50000000000000 : ℝ)*(upper3) + (17945407/20000000000000 : ℝ)*(upper5) + (202731420430199/20000000000000 : ℝ)*(major0) + (202731420430199/20000000000000 : ℝ)*(major1) + (202731420430199/20000000000000 : ℝ)*(major2) + (1340659568482803/100000000000000 : ℝ)*(sp0) + (670331635515157/50000000000000 : ℝ)*(sp1) + (67033158373597/5000000000000 : ℝ)*(sp2) + (343323899865937/50000000000000 : ℝ)*(sp3) + (4645680623/100000000000000 : ℝ)*(sp4) + (2062344503/100000000000000 : ℝ)*(sp7) + (686649941525591/100000000000000 : ℝ)*(f.failure) + (1340664134714211/100000000000000 : ℝ)*(f.sum) + (4680160821859/9389000000000000000000000000 : ℝ)*base65 + (4364794065403323007/1877800000000000000000000000000000 : ℝ)*base68 + (4711269889671523007/1877800000000000000000000000000000 : ℝ)*base70 + (7496671048681476993/1877800000000000000000000000000000 : ℝ)*base71 + (19242621071439/4694500000000000000000000000 : ℝ)*base74 + (1889113124928523007/1877800000000000000000000000000000 : ℝ)*base76 + (4457607583547876993/1877800000000000000000000000000000 : ℝ)*base77 + (1212291583100923007/1877800000000000000000000000000000 : ℝ)*base80 + (21131492448793/4694500000000000000000000000 : ℝ)*base82 + (21212429/5000000000000000000000 : ℝ)*base90 + (21212429/5000000000000000000000 : ℝ)*base92 + (21212429/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12008028385574852245371/4694500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2212111289/100000000000000 : ℝ)*(base19) + (521745701/25000000000000 : ℝ)*(base23) + (92382269/50000000000000 : ℝ)*(upper2) + (333986129/100000000000000 : ℝ)*(upper3) + (119803887/25000000000000 : ℝ)*(upper5) + (41739712662299/4000000000000 : ℝ)*(major0) + (41739712662299/4000000000000 : ℝ)*(major1) + (41739712662299/4000000000000 : ℝ)*(major2) + (1339314841/12500000000000 : ℝ)*(sp1) + (2287488473/20000000000000 : ℝ)*(sp2) + (43128904187197/3125000000000 : ℝ)*(sp4) + (690056003680143/50000000000000 : ℝ)*(sp5) + (690055704782567/50000000000000 : ℝ)*(sp6) + (706860613861543/100000000000000 : ℝ)*(sp7) + (706860613861543/100000000000000 : ℝ)*(f.failure) + (43128904187197/3125000000000 : ℝ)*(f.sum) + (5711303924837/1173625000000000000000000000 : ℝ)*base65 + (1518663975943858307/375560000000000000000000000000000 : ℝ)*base68 + (3053487520983378307/375560000000000000000000000000000 : ℝ)*base70 + (485443911672178307/375560000000000000000000000000000 : ℝ)*base72 + (3032345519453/4694500000000000000000000000 : ℝ)*base73 + (61813658209901693/375560000000000000000000000000000 : ℝ)*base75 + (1371679216031781693/375560000000000000000000000000000 : ℝ)*base77 + (117231387953261693/375560000000000000000000000000000 : ℝ)*base79 + (1184284481529/375560000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (26238083/5000000000000000000000 : ℝ)*base89 + (26238083/5000000000000000000000 : ℝ)*base91 + (26238083/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1047_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28183/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5101/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10441/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1047_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1047_s2_0 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2192235991/10000000000 : ℝ)*x 0 + (2764936921/5000000000 : ℝ)*x 1 + (128561669/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2192235991/10000000000 : ℝ)^515 ≤ (3317616738937/25000000000000 : ℝ)^387 := by
    have hnat : (2192235991 : ℕ)^515*25000000000000^387 ≤ 3317616738937^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192235991 10000000000 3317616738937 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2764936921/5000000000 : ℝ)^515 ≤ (45458850514363/100000000000000 : ℝ)^387 := by
    have hnat : (2764936921 : ℕ)^515*100000000000000^387 ≤ 45458850514363^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2764936921 5000000000 45458850514363 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128561669/250000000 : ℝ)^515 ≤ (41270682517671/100000000000000 : ℝ)^387 := by
    have hnat : (128561669 : ℕ)^515*100000000000000^387 ≤ 41270682517671^387*250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128561669 250000000 41270682517671 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2192235991/10000000000 : ℝ), (2764936921/5000000000 : ℝ), (128561669/250000000 : ℝ)] ![(3317616738937/25000000000000 : ℝ), (45458850514363/100000000000000 : ℝ), (41270682517671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2192235991/10000000000 : ℝ)|^515 ≤ (3317616738937/25000000000000 : ℝ)^387
        have hw : |(-2192235991/10000000000 : ℝ)|=(2192235991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2764936921/5000000000 : ℝ)|^515 ≤ (45458850514363/100000000000000 : ℝ)^387
        have hw : |(2764936921/5000000000 : ℝ)|=(2764936921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128561669/250000000 : ℝ)|^515 ≤ (41270682517671/100000000000000 : ℝ)^387
        have hw : |(128561669/250000000 : ℝ)|=(128561669/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s2_1 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5378056573/10000000000 : ℝ)*x 0 + (-299304749/1250000000 : ℝ)*x 1 + (5142469039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378056573/10000000000 : ℝ)^515 ≤ (43805624924019/100000000000000 : ℝ)^387 := by
    have hnat : (5378056573 : ℕ)^515*100000000000000^387 ≤ 43805624924019^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378056573 10000000000 43805624924019 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299304749/1250000000 : ℝ)^515 ≤ (3730917049851/25000000000000 : ℝ)^387 := by
    have hnat : (299304749 : ℕ)^515*25000000000000^387 ≤ 3730917049851^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299304749 1250000000 3730917049851 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5142469039/10000000000 : ℝ)^515 ≤ (20635353428561/50000000000000 : ℝ)^387 := by
    have hnat : (5142469039 : ℕ)^515*50000000000000^387 ≤ 20635353428561^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142469039 10000000000 20635353428561 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378056573/10000000000 : ℝ), (-299304749/1250000000 : ℝ), (5142469039/10000000000 : ℝ)] ![(43805624924019/100000000000000 : ℝ), (3730917049851/25000000000000 : ℝ), (20635353428561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378056573/10000000000 : ℝ)|^515 ≤ (43805624924019/100000000000000 : ℝ)^387
        have hw : |(5378056573/10000000000 : ℝ)|=(5378056573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-299304749/1250000000 : ℝ)|^515 ≤ (3730917049851/25000000000000 : ℝ)^387
        have hw : |(-299304749/1250000000 : ℝ)|=(299304749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5142469039/10000000000 : ℝ)|^515 ≤ (20635353428561/50000000000000 : ℝ)^387
        have hw : |(5142469039/10000000000 : ℝ)|=(5142469039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s2_2 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5378058139/10000000000 : ℝ)*x 0 + (5142466231/10000000000 : ℝ)*x 1 + (-1197219781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378058139/10000000000 : ℝ)^515 ≤ (8761128379669/20000000000000 : ℝ)^387 := by
    have hnat : (5378058139 : ℕ)^515*20000000000000^387 ≤ 8761128379669^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378058139 10000000000 8761128379669 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5142466231/10000000000 : ℝ)^515 ≤ (20635338434007/50000000000000 : ℝ)^387 := by
    have hnat : (5142466231 : ℕ)^515*50000000000000^387 ≤ 20635338434007^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142466231 10000000000 20635338434007 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1197219781/5000000000 : ℝ)^515 ≤ (1865460152639/12500000000000 : ℝ)^387 := by
    have hnat : (1197219781 : ℕ)^515*12500000000000^387 ≤ 1865460152639^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197219781 5000000000 1865460152639 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378058139/10000000000 : ℝ), (5142466231/10000000000 : ℝ), (-1197219781/5000000000 : ℝ)] ![(8761128379669/20000000000000 : ℝ), (20635338434007/50000000000000 : ℝ), (1865460152639/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378058139/10000000000 : ℝ)|^515 ≤ (8761128379669/20000000000000 : ℝ)^387
        have hw : |(5378058139/10000000000 : ℝ)|=(5378058139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5142466231/10000000000 : ℝ)|^515 ≤ (20635338434007/50000000000000 : ℝ)^387
        have hw : |(5142466231/10000000000 : ℝ)|=(5142466231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1197219781/5000000000 : ℝ)|^515 ≤ (1865460152639/12500000000000 : ℝ)^387
        have hw : |(-1197219781/5000000000 : ℝ)|=(1197219781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s2_3 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2182614793/5000000000 : ℝ)*x 0 + (200181249/500000000 : ℝ)*x 1 + (4760031971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182614793/5000000000 : ℝ)^515 ≤ (33184835383181/100000000000000 : ℝ)^387 := by
    have hnat : (2182614793 : ℕ)^515*100000000000000^387 ≤ 33184835383181^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182614793 5000000000 33184835383181 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200181249/500000000 : ℝ)^515 ≤ (29577748101231/100000000000000 : ℝ)^387 := by
    have hnat : (200181249 : ℕ)^515*100000000000000^387 ≤ 29577748101231^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200181249 500000000 29577748101231 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4760031971/10000000000 : ℝ)^515 ≤ (7447483299629/20000000000000 : ℝ)^387 := by
    have hnat : (4760031971 : ℕ)^515*20000000000000^387 ≤ 7447483299629^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4760031971 10000000000 7447483299629 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182614793/5000000000 : ℝ), (200181249/500000000 : ℝ), (4760031971/10000000000 : ℝ)] ![(33184835383181/100000000000000 : ℝ), (29577748101231/100000000000000 : ℝ), (7447483299629/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182614793/5000000000 : ℝ)|^515 ≤ (33184835383181/100000000000000 : ℝ)^387
        have hw : |(2182614793/5000000000 : ℝ)|=(2182614793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200181249/500000000 : ℝ)|^515 ≤ (29577748101231/100000000000000 : ℝ)^387
        have hw : |(200181249/500000000 : ℝ)|=(200181249/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4760031971/10000000000 : ℝ)|^515 ≤ (7447483299629/20000000000000 : ℝ)^387
        have hw : |(4760031971/10000000000 : ℝ)|=(4760031971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s2_4 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-548092291/2500000000 : ℝ)*x 0 + (5145322149/10000000000 : ℝ)*x 1 + (276349383/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548092291/2500000000 : ℝ)^515 ≤ (6635769874103/50000000000000 : ℝ)^387 := by
    have hnat : (548092291 : ℕ)^515*50000000000000^387 ≤ 6635769874103^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548092291 2500000000 6635769874103 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5145322149/10000000000 : ℝ)^515 ≤ (330409444263/800000000000 : ℝ)^387 := by
    have hnat : (5145322149 : ℕ)^515*800000000000^387 ≤ 330409444263^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5145322149 10000000000 330409444263 800000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276349383/500000000 : ℝ)^515 ≤ (45427279705213/100000000000000 : ℝ)^387 := by
    have hnat : (276349383 : ℕ)^515*100000000000000^387 ≤ 45427279705213^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276349383 500000000 45427279705213 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548092291/2500000000 : ℝ), (5145322149/10000000000 : ℝ), (276349383/500000000 : ℝ)] ![(6635769874103/50000000000000 : ℝ), (330409444263/800000000000 : ℝ), (45427279705213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548092291/2500000000 : ℝ)|^515 ≤ (6635769874103/50000000000000 : ℝ)^387
        have hw : |(-548092291/2500000000 : ℝ)|=(548092291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5145322149/10000000000 : ℝ)|^515 ≤ (330409444263/800000000000 : ℝ)^387
        have hw : |(5145322149/10000000000 : ℝ)|=(5145322149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276349383/500000000 : ℝ)|^515 ≤ (45427279705213/100000000000000 : ℝ)^387
        have hw : |(276349383/500000000 : ℝ)|=(276349383/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s2_5 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (660050507/1250000000 : ℝ)*x 0 + (-502479629/2500000000 : ℝ)*x 1 + (221079509/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660050507/1250000000 : ℝ)^515 ≤ (10687583126827/25000000000000 : ℝ)^387 := by
    have hnat : (660050507 : ℕ)^515*25000000000000^387 ≤ 10687583126827^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660050507 1250000000 10687583126827 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502479629/2500000000 : ℝ)^515 ≤ (2955596765249/25000000000000 : ℝ)^387 := by
    have hnat : (502479629 : ℕ)^515*25000000000000^387 ≤ 2955596765249^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502479629 2500000000 2955596765249 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221079509/400000000 : ℝ)^515 ≤ (45427280416161/100000000000000 : ℝ)^387 := by
    have hnat : (221079509 : ℕ)^515*100000000000000^387 ≤ 45427280416161^387*400000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221079509 400000000 45427280416161 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660050507/1250000000 : ℝ), (-502479629/2500000000 : ℝ), (221079509/400000000 : ℝ)] ![(10687583126827/25000000000000 : ℝ), (2955596765249/25000000000000 : ℝ), (45427280416161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660050507/1250000000 : ℝ)|^515 ≤ (10687583126827/25000000000000 : ℝ)^387
        have hw : |(660050507/1250000000 : ℝ)|=(660050507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-502479629/2500000000 : ℝ)|^515 ≤ (2955596765249/25000000000000 : ℝ)^387
        have hw : |(-502479629/2500000000 : ℝ)|=(502479629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(221079509/400000000 : ℝ)|^515 ≤ (45427280416161/100000000000000 : ℝ)^387
        have hw : |(221079509/400000000 : ℝ)|=(221079509/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s2_6 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2640202141/5000000000 : ℝ)*x 0 + (1105397513/2000000000 : ℝ)*x 1 + (-2009918429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640202141/5000000000 : ℝ)^515 ≤ (8550066988437/20000000000000 : ℝ)^387 := by
    have hnat : (2640202141 : ℕ)^515*20000000000000^387 ≤ 8550066988437^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640202141 5000000000 8550066988437 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105397513/2000000000 : ℝ)^515 ≤ (9085455733227/20000000000000 : ℝ)^387 := by
    have hnat : (1105397513 : ℕ)^515*20000000000000^387 ≤ 9085455733227^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105397513 2000000000 9085455733227 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2009918429/10000000000 : ℝ)^515 ≤ (11822386380003/100000000000000 : ℝ)^387 := by
    have hnat : (2009918429 : ℕ)^515*100000000000000^387 ≤ 11822386380003^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009918429 10000000000 11822386380003 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640202141/5000000000 : ℝ), (1105397513/2000000000 : ℝ), (-2009918429/10000000000 : ℝ)] ![(8550066988437/20000000000000 : ℝ), (9085455733227/20000000000000 : ℝ), (11822386380003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640202141/5000000000 : ℝ)|^515 ≤ (8550066988437/20000000000000 : ℝ)^387
        have hw : |(2640202141/5000000000 : ℝ)|=(2640202141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1105397513/2000000000 : ℝ)|^515 ≤ (9085455733227/20000000000000 : ℝ)^387
        have hw : |(1105397513/2000000000 : ℝ)|=(1105397513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2009918429/10000000000 : ℝ)|^515 ≤ (11822386380003/100000000000000 : ℝ)^387
        have hw : |(-2009918429/10000000000 : ℝ)|=(2009918429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s2_7 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4365491313/10000000000 : ℝ)*x 0 + (4754452463/10000000000 : ℝ)*x 1 + (2004630691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365491313/10000000000 : ℝ)^515 ≤ (1327499326473/4000000000000 : ℝ)^387 := by
    have hnat : (4365491313 : ℕ)^515*4000000000000^387 ≤ 1327499326473^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365491313 10000000000 1327499326473 4000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4754452463/10000000000 : ℝ)^515 ≤ (7435868609681/20000000000000 : ℝ)^387 := by
    have hnat : (4754452463 : ℕ)^515*20000000000000^387 ≤ 7435868609681^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4754452463 10000000000 7435868609681 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2004630691/5000000000 : ℝ)^515 ≤ (1481658688923/5000000000000 : ℝ)^387 := by
    have hnat : (2004630691 : ℕ)^515*5000000000000^387 ≤ 1481658688923^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004630691 5000000000 1481658688923 5000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365491313/10000000000 : ℝ), (4754452463/10000000000 : ℝ), (2004630691/5000000000 : ℝ)] ![(1327499326473/4000000000000 : ℝ), (7435868609681/20000000000000 : ℝ), (1481658688923/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365491313/10000000000 : ℝ)|^515 ≤ (1327499326473/4000000000000 : ℝ)^387
        have hw : |(4365491313/10000000000 : ℝ)|=(4365491313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4754452463/10000000000 : ℝ)|^515 ≤ (7435868609681/20000000000000 : ℝ)^387
        have hw : |(4754452463/10000000000 : ℝ)|=(4754452463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2004630691/5000000000 : ℝ)|^515 ≤ (1481658688923/5000000000000 : ℝ)^387
        have hw : |(2004630691/5000000000 : ℝ)|=(2004630691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1047_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10441/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4309/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4201/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10441/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10441/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10441/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10441/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10441/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10441/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (5101/100000 : ℝ) ^ (8239/2048 : ℝ) ≤ (632357965387693/100000000000000000000 : ℝ) := by
    have hpowers : (5101/100000 : ℝ)^8239 ≤ (632357965387693/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5101 : ℕ)^8239*100000000000000000000^2048 ≤ 632357965387693^2048*100000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5101 100000 632357965387693 100000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5101/100000 : ℝ)) (X := (632357965387693/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10441/50000 : ℝ) ^ (8239/2048 : ℝ) ≤ (22929135439767457/12500000000000000000 : ℝ) := by
    have hpowers : (10441/50000 : ℝ)^8239 ≤ (22929135439767457/12500000000000000000 : ℝ)^2048 := by
      have hnat : (10441 : ℕ)^8239*12500000000000000000^2048 ≤ 22929135439767457^2048*50000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10441 50000 22929135439767457 12500000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10441/50000 : ℝ)) (X := (22929135439767457/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000632357965387693/50000000000000000000 : ℝ) ≤ (625001964836387/625000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (50000632357965387693/50000000000000000000 : ℝ)^2048 ≤ (625001964836387/625000000000000 : ℝ)^8239 := by
      have hnat : (50000632357965387693 : ℕ)^2048*625000000000000^8239 ≤ 625001964836387^8239*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000632357965387693 50000000000000000000 625001964836387 625000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625001964836387/625000000000000 : ℝ)) (X := (50000632357965387693/50000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100184065441483527349/100000000000000000000 : ℝ) ≤ (10004572224907171/10000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (100184065441483527349/100000000000000000000 : ℝ)^2048 ≤ (10004572224907171/10000000000000000 : ℝ)^8239 := by
      have hnat : (100184065441483527349 : ℕ)^2048*10000000000000000^8239 ≤ 10004572224907171^8239*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100184065441483527349 100000000000000000000 10004572224907171 10000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004572224907171/10000000000000000 : ℝ)) (X := (100184065441483527349/100000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6272929135439767457/6250000000000000000 : ℝ) ≤ (200182260248643/200000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (6272929135439767457/6250000000000000000 : ℝ)^2048 ≤ (200182260248643/200000000000000 : ℝ)^8239 := by
      have hnat : (6272929135439767457 : ℕ)^2048*200000000000000^8239 ≤ 200182260248643^8239*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6272929135439767457 6250000000000000000 200182260248643 200000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200182260248643/200000000000000 : ℝ)) (X := (6272929135439767457/6250000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(632357965387693/100000000000000000000 : ℝ) ≤ ((78882085499499268097/78905000000000000000 : ℝ)+2*(4540787524979/1578100000000000 : ℝ)*(5101/100000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (78882085499499268097/78905000000000000000 : ℝ)+2*(4540787524979/1578100000000000 : ℝ)*(5101/100000 : ℝ)=(625001964836387/625000000000000 : ℝ) by norm_num, show 1+2*(632357965387693/100000000000000000000 : ℝ)=(50000632357965387693/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22929135439767457/12500000000000000000 : ℝ)+(632357965387693/100000000000000000000 : ℝ) ≤ ((78882085499499268097/78905000000000000000 : ℝ)+(4540787524979/1578100000000000 : ℝ)*((10441/50000 : ℝ)+(5101/100000 : ℝ)))^(8239/2048 : ℝ) := by
    rw [show (78882085499499268097/78905000000000000000 : ℝ)+(4540787524979/1578100000000000 : ℝ)*((10441/50000 : ℝ)+(5101/100000 : ℝ))=(10004572224907171/10000000000000000 : ℝ) by norm_num, show 1+(22929135439767457/12500000000000000000 : ℝ)+(632357965387693/100000000000000000000 : ℝ)=(100184065441483527349/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22929135439767457/12500000000000000000 : ℝ) ≤ ((78882085499499268097/78905000000000000000 : ℝ)+2*(4540787524979/1578100000000000 : ℝ)*(10441/50000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (78882085499499268097/78905000000000000000 : ℝ)+2*(4540787524979/1578100000000000 : ℝ)*(10441/50000 : ℝ)=(200182260248643/200000000000000 : ℝ) by norm_num, show 1+2*(22929135439767457/12500000000000000000 : ℝ)=(6272929135439767457/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (78882085499499268097/78905000000000000000 : ℝ)*(X 1 0+X 2 0)+(4540787524979/1578100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (5101/100000 : ℝ)) (hi := (10441/50000 : ℝ)) (c := (78882085499499268097/78905000000000000000 : ℝ)) (alpha := (4540787524979/1578100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (78882085499499268097/78905000000000000000 : ℝ)*(X 0 1+X 2 1)+(4540787524979/1578100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (5101/100000 : ℝ)) (hi := (10441/50000 : ℝ)) (c := (78882085499499268097/78905000000000000000 : ℝ)) (alpha := (4540787524979/1578100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (78882085499499268097/78905000000000000000 : ℝ)*(X 0 2+X 1 2)+(4540787524979/1578100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (5101/100000 : ℝ)) (hi := (10441/50000 : ℝ)) (c := (78882085499499268097/78905000000000000000 : ℝ)) (alpha := (4540787524979/1578100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2192235991/10000000000 : ℝ)*X 0 0+(2764936921/5000000000 : ℝ)*X 0 1+(128561669/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5378056573/10000000000 : ℝ)*X 1 0+(-299304749/1250000000 : ℝ)*X 1 1+(5142469039/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5378058139/10000000000 : ℝ)*X 2 0+(5142466231/10000000000 : ℝ)*X 2 1+(-1197219781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182614793/5000000000 : ℝ)*X 0 0+(200181249/500000000 : ℝ)*X 0 1+(4760031971/10000000000 : ℝ)*X 0 2+(2182614793/5000000000 : ℝ)*X 1 0+(200181249/500000000 : ℝ)*X 1 1+(4760031971/10000000000 : ℝ)*X 1 2+(2182614793/5000000000 : ℝ)*X 2 0+(200181249/500000000 : ℝ)*X 2 1+(4760031971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-548092291/2500000000 : ℝ)*X 0 0+(5145322149/10000000000 : ℝ)*X 0 1+(276349383/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((660050507/1250000000 : ℝ)*X 1 0+(-502479629/2500000000 : ℝ)*X 1 1+(221079509/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640202141/5000000000 : ℝ)*X 2 0+(1105397513/2000000000 : ℝ)*X 2 1+(-2009918429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365491313/10000000000 : ℝ)*X 0 0+(4754452463/10000000000 : ℝ)*X 0 1+(2004630691/5000000000 : ℝ)*X 0 2+(4365491313/10000000000 : ℝ)*X 1 0+(4754452463/10000000000 : ℝ)*X 1 1+(2004630691/5000000000 : ℝ)*X 1 2+(4365491313/10000000000 : ℝ)*X 2 0+(4754452463/10000000000 : ℝ)*X 2 1+(2004630691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (367918362724884704342937/78905000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36577113/20000000000000 : ℝ)*(base15) + (1873089/100000000000000 : ℝ)*(lower2) + (211577879/100000000000000 : ℝ)*(upper4) + (209499269/100000000000000 : ℝ)*(lower5) + (487919071992251/25000000000000 : ℝ)*(major0) + (487919071992251/25000000000000 : ℝ)*(major1) + (487919071992251/25000000000000 : ℝ)*(major2) + (1290638352987789/50000000000000 : ℝ)*(sp0) + (1290644688081967/50000000000000 : ℝ)*(sp1) + (1290639339375909/50000000000000 : ℝ)*(sp2) + (165256244475113/12500000000000 : ℝ)*(sp3) + (12853073921/100000000000000 : ℝ)*(sp4) + (136003721/1250000000000 : ℝ)*(sp6) + (103245287/800000000000 : ℝ)*(sp7) + (66103143073089/5000000000000 : ℝ)*(f.failure) + (1290644779524749/50000000000000 : ℝ)*(f.sum) + (966859536721731/78905000000000000000000000000 : ℝ)*base65 + (13632753315076783653/1972625000000000000000000000000000 : ℝ)*base68 + (11980204916819783653/1972625000000000000000000000000000 : ℝ)*base70 + (10823676165219341347/1972625000000000000000000000000000 : ℝ)*base71 + (76774426872969/78905000000000000000000000000 : ℝ)*base74 + (7071992943115533653/1972625000000000000000000000000000 : ℝ)*base76 + (20117946851134341347/1972625000000000000000000000000000 : ℝ)*base77 + (6439494610849091347/1972625000000000000000000000000000 : ℝ)*base79 + (68833789477863/39452500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2261509/250000000000000000000 : ℝ)*base89 + (2261509/250000000000000000000 : ℝ)*base91 + (2261509/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10711841122853592555069542667/1972625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6396611/625000000000 : ℝ)*(base19) + (150477219/12500000000000 : ℝ)*(base23) + (897309/625000000000 : ℝ)*(upper3) + (5404159/25000000000000 : ℝ)*(lower4) + (30598829/25000000000000 : ℝ)*(upper5) + (1981016687517937/100000000000000 : ℝ)*(major0) + (1981016687517937/100000000000000 : ℝ)*(major1) + (1981016687517937/100000000000000 : ℝ)*(major2) + (8614798263/100000000000000 : ℝ)*(sp1) + (2017990483/20000000000000 : ℝ)*(sp2) + (163755949115021/6250000000000 : ℝ)*(sp4) + (327510693448039/12500000000000 : ℝ)*(sp5) + (327510486508771/12500000000000 : ℝ)*(sp6) + (41935562755853/3125000000000 : ℝ)*(sp7) + (41935562755853/3125000000000 : ℝ)*(f.failure) + (163755949115021/6250000000000 : ℝ)*(f.sum) + (119532875324003/78905000000000000000000000000 : ℝ)*base65 + (30204845230260494111/7890500000000000000000000000000000 : ℝ)*base68 + (74451176843420494111/7890500000000000000000000000000000 : ℝ)*base70 + (14620710893343994111/7890500000000000000000000000000000 : ℝ)*base72 + (116485515618523/78905000000000000000000000000 : ℝ)*base73 + (48671301290598994111/7890500000000000000000000000000000 : ℝ)*base76 + (38940911701888994111/7890500000000000000000000000000000 : ℝ)*base78 + (7831651512689005889/7890500000000000000000000000000000 : ℝ)*base79 + (305518435478527/78905000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1541693/156250000000000000000 : ℝ)*base89 + (1541693/156250000000000000000 : ℝ)*base91 + (1541693/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1047_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10441/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4309/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4201/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1047_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1047_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4309/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4201/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1047_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1047_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1047_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4309/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4201/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1047_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
