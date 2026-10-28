-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1036_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:42:38.67118+00:00
-- url     : https://prove2.me/submissions/8e16a526-8503-4977-b483-3a51445bf10c

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
theorem support_rectangle_w1036_s0_0 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1369037387/2500000000 : ℝ)*x 0 + (-2707503743/10000000000 : ℝ)*x 1 + (4794699273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1369037387/2500000000 : ℝ)^8229 ≤ (1121404371719/2500000000000 : ℝ)^6181 := by
    have hnat : (1369037387 : ℕ)^8229*2500000000000^6181 ≤ 1121404371719^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369037387 2500000000 1121404371719 2500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707503743/10000000000 : ℝ)^8229 ≤ (17561339995549/100000000000000 : ℝ)^6181 := by
    have hnat : (2707503743 : ℕ)^8229*100000000000000^6181 ≤ 17561339995549^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707503743 10000000000 17561339995549 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4794699273/10000000000 : ℝ)^8229 ≤ (2348905319707/6250000000000 : ℝ)^6181 := by
    have hnat : (4794699273 : ℕ)^8229*6250000000000^6181 ≤ 2348905319707^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794699273 10000000000 2348905319707 6250000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1369037387/2500000000 : ℝ), (-2707503743/10000000000 : ℝ), (4794699273/10000000000 : ℝ)] ![(1121404371719/2500000000000 : ℝ), (17561339995549/100000000000000 : ℝ), (2348905319707/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1369037387/2500000000 : ℝ)|^8229 ≤ (1121404371719/2500000000000 : ℝ)^6181
        have hw : |(1369037387/2500000000 : ℝ)|=(1369037387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2707503743/10000000000 : ℝ)|^8229 ≤ (17561339995549/100000000000000 : ℝ)^6181
        have hw : |(-2707503743/10000000000 : ℝ)|=(2707503743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4794699273/10000000000 : ℝ)|^8229 ≤ (2348905319707/6250000000000 : ℝ)^6181
        have hw : |(4794699273/10000000000 : ℝ)|=(4794699273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s0_1 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5474639161/10000000000 : ℝ)*x 0 + (4791427509/10000000000 : ℝ)*x 1 + (-2713362357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5474639161/10000000000 : ℝ)^8229 ≤ (11209926121917/25000000000000 : ℝ)^6181 := by
    have hnat : (5474639161 : ℕ)^8229*25000000000000^6181 ≤ 11209926121917^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474639161 10000000000 11209926121917 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4791427509/10000000000 : ℝ)^8229 ≤ (18774173273537/50000000000000 : ℝ)^6181 := by
    have hnat : (4791427509 : ℕ)^8229*50000000000000^6181 ≤ 18774173273537^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4791427509 10000000000 18774173273537 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713362357/10000000000 : ℝ)^8229 ≤ (137593351179/781250000000 : ℝ)^6181 := by
    have hnat : (2713362357 : ℕ)^8229*781250000000^6181 ≤ 137593351179^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713362357 10000000000 137593351179 781250000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5474639161/10000000000 : ℝ), (4791427509/10000000000 : ℝ), (-2713362357/10000000000 : ℝ)] ![(11209926121917/25000000000000 : ℝ), (18774173273537/50000000000000 : ℝ), (137593351179/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5474639161/10000000000 : ℝ)|^8229 ≤ (11209926121917/25000000000000 : ℝ)^6181
        have hw : |(5474639161/10000000000 : ℝ)|=(5474639161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4791427509/10000000000 : ℝ)|^8229 ≤ (18774173273537/50000000000000 : ℝ)^6181
        have hw : |(4791427509/10000000000 : ℝ)|=(4791427509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2713362357/10000000000 : ℝ)|^8229 ≤ (137593351179/781250000000 : ℝ)^6181
        have hw : |(-2713362357/10000000000 : ℝ)|=(2713362357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s0_2 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1931282607/10000000000 : ℝ)*x 0 + (300050971/625000000 : ℝ)*x 1 + (6044079323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1931282607/10000000000 : ℝ)^8229 ≤ (11200036428603/100000000000000 : ℝ)^6181 := by
    have hnat : (1931282607 : ℕ)^8229*100000000000000^6181 ≤ 11200036428603^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931282607 10000000000 11200036428603 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300050971/625000000 : ℝ)^8229 ≤ (37646324741643/100000000000000 : ℝ)^6181 := by
    have hnat : (300050971 : ℕ)^8229*100000000000000^6181 ≤ 37646324741643^6181*625000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300050971 625000000 37646324741643 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6044079323/10000000000 : ℝ)^8229 ≤ (10230727764481/20000000000000 : ℝ)^6181 := by
    have hnat : (6044079323 : ℕ)^8229*20000000000000^6181 ≤ 10230727764481^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6044079323 10000000000 10230727764481 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1931282607/10000000000 : ℝ), (300050971/625000000 : ℝ), (6044079323/10000000000 : ℝ)] ![(11200036428603/100000000000000 : ℝ), (37646324741643/100000000000000 : ℝ), (10230727764481/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1931282607/10000000000 : ℝ)|^8229 ≤ (11200036428603/100000000000000 : ℝ)^6181
        have hw : |(-1931282607/10000000000 : ℝ)|=(1931282607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(300050971/625000000 : ℝ)|^8229 ≤ (37646324741643/100000000000000 : ℝ)^6181
        have hw : |(300050971/625000000 : ℝ)|=(300050971/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6044079323/10000000000 : ℝ)|^8229 ≤ (10230727764481/20000000000000 : ℝ)^6181
        have hw : |(6044079323/10000000000 : ℝ)|=(6044079323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s0_3 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1291692399/2500000000 : ℝ)*x 0 + (-1404895743/10000000000 : ℝ)*x 1 + (3022039671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1291692399/2500000000 : ℝ)^8229 ≤ (41514297395683/100000000000000 : ℝ)^6181 := by
    have hnat : (1291692399 : ℕ)^8229*100000000000000^6181 ≤ 41514297395683^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291692399 2500000000 41514297395683 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1404895743/10000000000 : ℝ)^8229 ≤ (7332063553899/100000000000000 : ℝ)^6181 := by
    have hnat : (1404895743 : ℕ)^8229*100000000000000^6181 ≤ 7332063553899^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404895743 10000000000 7332063553899 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3022039671/5000000000 : ℝ)^8229 ≤ (51153639036491/100000000000000 : ℝ)^6181 := by
    have hnat : (3022039671 : ℕ)^8229*100000000000000^6181 ≤ 51153639036491^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3022039671 5000000000 51153639036491 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1291692399/2500000000 : ℝ), (-1404895743/10000000000 : ℝ), (3022039671/5000000000 : ℝ)] ![(41514297395683/100000000000000 : ℝ), (7332063553899/100000000000000 : ℝ), (51153639036491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1291692399/2500000000 : ℝ)|^8229 ≤ (41514297395683/100000000000000 : ℝ)^6181
        have hw : |(1291692399/2500000000 : ℝ)|=(1291692399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1404895743/10000000000 : ℝ)|^8229 ≤ (7332063553899/100000000000000 : ℝ)^6181
        have hw : |(-1404895743/10000000000 : ℝ)|=(1404895743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3022039671/5000000000 : ℝ)|^8229 ≤ (51153639036491/100000000000000 : ℝ)^6181
        have hw : |(3022039671/5000000000 : ℝ)|=(3022039671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s0_4 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5166769659/10000000000 : ℝ)*x 0 + (6044079317/10000000000 : ℝ)*x 1 + (-702447843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5166769659/10000000000 : ℝ)^8229 ≤ (20757149034801/50000000000000 : ℝ)^6181 := by
    have hnat : (5166769659 : ℕ)^8229*50000000000000^6181 ≤ 20757149034801^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166769659 10000000000 20757149034801 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6044079317/10000000000 : ℝ)^8229 ≤ (51153638754799/100000000000000 : ℝ)^6181 := by
    have hnat : (6044079317 : ℕ)^8229*100000000000000^6181 ≤ 51153638754799^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6044079317 10000000000 51153638754799 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (702447843/5000000000 : ℝ)^8229 ≤ (7332063157853/100000000000000 : ℝ)^6181 := by
    have hnat : (702447843 : ℕ)^8229*100000000000000^6181 ≤ 7332063157853^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702447843 5000000000 7332063157853 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5166769659/10000000000 : ℝ), (6044079317/10000000000 : ℝ), (-702447843/5000000000 : ℝ)] ![(20757149034801/50000000000000 : ℝ), (51153638754799/100000000000000 : ℝ), (7332063157853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5166769659/10000000000 : ℝ)|^8229 ≤ (20757149034801/50000000000000 : ℝ)^6181
        have hw : |(5166769659/10000000000 : ℝ)|=(5166769659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6044079317/10000000000 : ℝ)|^8229 ≤ (51153638754799/100000000000000 : ℝ)^6181
        have hw : |(6044079317/10000000000 : ℝ)|=(6044079317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-702447843/5000000000 : ℝ)|^8229 ≤ (7332063157853/100000000000000 : ℝ)^6181
        have hw : |(-702447843/5000000000 : ℝ)|=(702447843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s0_5 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4220351093/10000000000 : ℝ)*x 0 + (2808483817/5000000000 : ℝ)*x 1 + (3194846551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4220351093/10000000000 : ℝ)^8229 ≤ (7927793867513/25000000000000 : ℝ)^6181 := by
    have hnat : (4220351093 : ℕ)^8229*25000000000000^6181 ≤ 7927793867513^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220351093 10000000000 7927793867513 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2808483817/5000000000 : ℝ)^8229 ≤ (46398335003007/100000000000000 : ℝ)^6181 := by
    have hnat : (2808483817 : ℕ)^8229*100000000000000^6181 ≤ 46398335003007^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2808483817 5000000000 46398335003007 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3194846551/10000000000 : ℝ)^8229 ≤ (21890489515521/100000000000000 : ℝ)^6181 := by
    have hnat : (3194846551 : ℕ)^8229*100000000000000^6181 ≤ 21890489515521^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3194846551 10000000000 21890489515521 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4220351093/10000000000 : ℝ), (2808483817/5000000000 : ℝ), (3194846551/10000000000 : ℝ)] ![(7927793867513/25000000000000 : ℝ), (46398335003007/100000000000000 : ℝ), (21890489515521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4220351093/10000000000 : ℝ)|^8229 ≤ (7927793867513/25000000000000 : ℝ)^6181
        have hw : |(4220351093/10000000000 : ℝ)|=(4220351093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2808483817/5000000000 : ℝ)|^8229 ≤ (46398335003007/100000000000000 : ℝ)^6181
        have hw : |(2808483817/5000000000 : ℝ)|=(2808483817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3194846551/10000000000 : ℝ)|^8229 ≤ (21890489515521/100000000000000 : ℝ)^6181
        have hw : |(3194846551/10000000000 : ℝ)|=(3194846551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1036_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (0 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28227/100000 : ℝ)*pair X 0 0 := by
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
  have base43 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [sign0]
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
  have hpowlo : (0 : ℝ) ^ (2057/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2057 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2057*1^512 ≤ 0^512*1^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2057/512 : ℝ) ≤ (629774301324699741/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2057 ≤ (629774301324699741/25000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2057*25000000000000000000^512 ≤ 629774301324699741^512*5^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 629774301324699741 25000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (629774301324699741/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2057 := by
      have hnat : (1 : ℕ)^512*1^2057 ≤ 1^2057*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25629774301324699741/25000000000000000000 : ℝ) ≤ (2515529318540791/2500000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (25629774301324699741/25000000000000000000 : ℝ)^512 ≤ (2515529318540791/2500000000000000 : ℝ)^2057 := by
      have hnat : (25629774301324699741 : ℕ)^512*2500000000000000^2057 ≤ 2515529318540791^2057*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25629774301324699741 25000000000000000000 2515529318540791 2500000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2515529318540791/2500000000000000 : ℝ)) (X := (25629774301324699741/25000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (13129774301324699741/12500000000000000000 : ℝ) ≤ (1265529318540791/1250000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (13129774301324699741/12500000000000000000 : ℝ)^512 ≤ (1265529318540791/1250000000000000 : ℝ)^2057 := by
      have hnat : (13129774301324699741 : ℕ)^512*1250000000000000^2057 ≤ 1265529318540791^2057*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13129774301324699741 12500000000000000000 1265529318540791 1250000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1265529318540791/1250000000000000 : ℝ)) (X := (13129774301324699741/12500000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15529318540791/1000000000000000 : ℝ)*(0 : ℝ))^(2057/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(15529318540791/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(629774301324699741/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15529318540791/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2057/512 : ℝ) := by
    rw [show (1 : ℝ)+(15529318540791/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2515529318540791/2500000000000000 : ℝ) by norm_num, show 1+(629774301324699741/25000000000000000000 : ℝ)+(0 : ℝ)=(25629774301324699741/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(629774301324699741/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15529318540791/1000000000000000 : ℝ)*(2/5 : ℝ))^(2057/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(15529318540791/1000000000000000 : ℝ)*(2/5 : ℝ)=(1265529318540791/1250000000000000 : ℝ) by norm_num, show 1+2*(629774301324699741/25000000000000000000 : ℝ)=(13129774301324699741/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15529318540791/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15529318540791/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15529318540791/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15529318540791/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15529318540791/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15529318540791/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1369037387/2500000000 : ℝ)*X 1 0+(-2707503743/10000000000 : ℝ)*X 1 1+(4794699273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s0_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5474639161/10000000000 : ℝ)*X 2 0+(4791427509/10000000000 : ℝ)*X 2 1+(-2713362357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s0_1 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1931282607/10000000000 : ℝ)*X 0 0+(300050971/625000000 : ℝ)*X 0 1+(6044079323/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s0_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1291692399/2500000000 : ℝ)*X 1 0+(-1404895743/10000000000 : ℝ)*X 1 1+(3022039671/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s0_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5166769659/10000000000 : ℝ)*X 2 0+(6044079317/10000000000 : ℝ)*X 2 1+(-702447843/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s0_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4220351093/10000000000 : ℝ)*X 0 0+(2808483817/5000000000 : ℝ)*X 0 1+(3194846551/10000000000 : ℝ)*X 0 2+(4220351093/10000000000 : ℝ)*X 1 0+(2808483817/5000000000 : ℝ)*X 1 1+(3194846551/10000000000 : ℝ)*X 1 2+(4220351093/10000000000 : ℝ)*X 2 0+(2808483817/5000000000 : ℝ)*X 2 1+(3194846551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s0_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(base43) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24864198569638272476331/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83570417/100000000000000 : ℝ)*(base1) + (1941425971/100000000000000 : ℝ)*(base19) + (1951161649/100000000000000 : ℝ)*(base23) + (226347973/100000000000000 : ℝ)*(upper3) + (225591449/100000000000000 : ℝ)*(upper5) + (38037377873511/6250000000000 : ℝ)*(major0) + (38037377873511/6250000000000 : ℝ)*(major1) + (38037377873511/6250000000000 : ℝ)*(major2) + (985853629/25000000000000 : ℝ)*(sp0) + (3961556579/100000000000000 : ℝ)*(sp1) + (80433454276829/10000000000000 : ℝ)*(sp2) + (402164287178693/50000000000000 : ℝ)*(sp3) + (402164273239823/50000000000000 : ℝ)*(sp4) + (20643064198297/5000000000000 : ℝ)*(sp5) + (412861367536357/100000000000000 : ℝ)*(f.failure) + (804334459197873/100000000000000 : ℝ)*(f.sum) + (6492034331549/3125000000000000000000000000 : ℝ)*base66 + (5097220637201/6250000000000000000000000000 : ℝ)*base67 + (1590963074701/6250000000000000000000000000 : ℝ)*base69 + (32421546612201/6250000000000000000000000000 : ℝ)*base71 + (16398923031549/3125000000000000000000000000 : ℝ)*base74 + (2331593012201/6250000000000000000000000000 : ℝ)*base75 + (2150804069049/6250000000000000000000000000 : ℝ)*base78 + (54593154694049/6250000000000000000000000000 : ℝ)*base80 + (2504515372731/781250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (29980531/10000000000000000000000 : ℝ)*base89 + (29980531/10000000000000000000000 : ℝ)*base91 + (29980531/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1036_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28227/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1036_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1036_s1_0 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-267254613/1250000000 : ℝ)*x 0 + (5730578977/10000000000 : ℝ)*x 1 + (995916721/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267254613/1250000000 : ℝ)^8229 ≤ (6412004170979/50000000000000 : ℝ)^6181 := by
    have hnat : (267254613 : ℕ)^8229*50000000000000^6181 ≤ 6412004170979^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267254613 1250000000 6412004170979 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5730578977/10000000000 : ℝ)^8229 ≤ (23825964416521/50000000000000 : ℝ)^6181 := by
    have hnat : (5730578977 : ℕ)^8229*50000000000000^6181 ≤ 23825964416521^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5730578977 10000000000 23825964416521 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995916721/2000000000 : ℝ)^8229 ≤ (19762031402797/50000000000000 : ℝ)^6181 := by
    have hnat : (995916721 : ℕ)^8229*50000000000000^6181 ≤ 19762031402797^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995916721 2000000000 19762031402797 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267254613/1250000000 : ℝ), (5730578977/10000000000 : ℝ), (995916721/2000000000 : ℝ)] ![(6412004170979/50000000000000 : ℝ), (23825964416521/50000000000000 : ℝ), (19762031402797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267254613/1250000000 : ℝ)|^8229 ≤ (6412004170979/50000000000000 : ℝ)^6181
        have hw : |(-267254613/1250000000 : ℝ)|=(267254613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5730578977/10000000000 : ℝ)|^8229 ≤ (23825964416521/50000000000000 : ℝ)^6181
        have hw : |(5730578977/10000000000 : ℝ)|=(5730578977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(995916721/2000000000 : ℝ)|^8229 ≤ (19762031402797/50000000000000 : ℝ)^6181
        have hw : |(995916721/2000000000 : ℝ)|=(995916721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s1_1 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2712486219/5000000000 : ℝ)*x 0 + (-159097767/625000000 : ℝ)*x 1 + (2489791961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2712486219/5000000000 : ℝ)^8229 ≤ (22149471025527/50000000000000 : ℝ)^6181 := by
    have hnat : (2712486219 : ℕ)^8229*50000000000000^6181 ≤ 22149471025527^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712486219 5000000000 22149471025527 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (159097767/625000000 : ℝ)^8229 ≤ (2022123973847/12500000000000 : ℝ)^6181 := by
    have hnat : (159097767 : ℕ)^8229*12500000000000^6181 ≤ 2022123973847^6181*625000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159097767 625000000 2022123973847 12500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2489791961/5000000000 : ℝ)^8229 ≤ (39524066155373/100000000000000 : ℝ)^6181 := by
    have hnat : (2489791961 : ℕ)^8229*100000000000000^6181 ≤ 39524066155373^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2489791961 5000000000 39524066155373 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2712486219/5000000000 : ℝ), (-159097767/625000000 : ℝ), (2489791961/5000000000 : ℝ)] ![(22149471025527/50000000000000 : ℝ), (2022123973847/12500000000000 : ℝ), (39524066155373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2712486219/5000000000 : ℝ)|^8229 ≤ (22149471025527/50000000000000 : ℝ)^6181
        have hw : |(2712486219/5000000000 : ℝ)|=(2712486219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-159097767/625000000 : ℝ)|^8229 ≤ (2022123973847/12500000000000 : ℝ)^6181
        have hw : |(-159097767/625000000 : ℝ)|=(159097767/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2489791961/5000000000 : ℝ)|^8229 ≤ (39524066155373/100000000000000 : ℝ)^6181
        have hw : |(2489791961/5000000000 : ℝ)|=(2489791961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s1_2 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (271248639/500000000 : ℝ)*x 0 + (4979583481/10000000000 : ℝ)*x 1 + (-1272782191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271248639/500000000 : ℝ)^8229 ≤ (44298945769061/100000000000000 : ℝ)^6181 := by
    have hnat : (271248639 : ℕ)^8229*100000000000000^6181 ≤ 44298945769061^6181*500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271248639 500000000 44298945769061 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4979583481/10000000000 : ℝ)^8229 ≤ (39524061495271/100000000000000 : ℝ)^6181 := by
    have hnat : (4979583481 : ℕ)^8229*100000000000000^6181 ≤ 39524061495271^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4979583481 10000000000 39524061495271 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1272782191/5000000000 : ℝ)^8229 ≤ (4044248180361/25000000000000 : ℝ)^6181 := by
    have hnat : (1272782191 : ℕ)^8229*25000000000000^6181 ≤ 4044248180361^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272782191 5000000000 4044248180361 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271248639/500000000 : ℝ), (4979583481/10000000000 : ℝ), (-1272782191/5000000000 : ℝ)] ![(44298945769061/100000000000000 : ℝ), (39524061495271/100000000000000 : ℝ), (4044248180361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271248639/500000000 : ℝ)|^8229 ≤ (44298945769061/100000000000000 : ℝ)^6181
        have hw : |(271248639/500000000 : ℝ)|=(271248639/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4979583481/10000000000 : ℝ)|^8229 ≤ (39524061495271/100000000000000 : ℝ)^6181
        have hw : |(4979583481/10000000000 : ℝ)|=(4979583481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1272782191/5000000000 : ℝ)|^8229 ≤ (4044248180361/25000000000000 : ℝ)^6181
        have hw : |(-1272782191/5000000000 : ℝ)|=(1272782191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s1_3 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2163174663/5000000000 : ℝ)*x 0 + (3657207157/10000000000 : ℝ)*x 1 + (5120291771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163174663/5000000000 : ℝ)^8229 ≤ (819397916587/2500000000000 : ℝ)^6181 := by
    have hnat : (2163174663 : ℕ)^8229*2500000000000^6181 ≤ 819397916587^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163174663 5000000000 819397916587 2500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3657207157/10000000000 : ℝ)^8229 ≤ (26206222427623/100000000000000 : ℝ)^6181 := by
    have hnat : (3657207157 : ℕ)^8229*100000000000000^6181 ≤ 26206222427623^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3657207157 10000000000 26206222427623 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5120291771/10000000000 : ℝ)^8229 ≤ (10254465224147/25000000000000 : ℝ)^6181 := by
    have hnat : (5120291771 : ℕ)^8229*25000000000000^6181 ≤ 10254465224147^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5120291771 10000000000 10254465224147 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163174663/5000000000 : ℝ), (3657207157/10000000000 : ℝ), (5120291771/10000000000 : ℝ)] ![(819397916587/2500000000000 : ℝ), (26206222427623/100000000000000 : ℝ), (10254465224147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163174663/5000000000 : ℝ)|^8229 ≤ (819397916587/2500000000000 : ℝ)^6181
        have hw : |(2163174663/5000000000 : ℝ)|=(2163174663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3657207157/10000000000 : ℝ)|^8229 ≤ (26206222427623/100000000000000 : ℝ)^6181
        have hw : |(3657207157/10000000000 : ℝ)|=(3657207157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5120291771/10000000000 : ℝ)|^8229 ≤ (10254465224147/25000000000000 : ℝ)^6181
        have hw : |(5120291771/10000000000 : ℝ)|=(5120291771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s1_4 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139005271/10000000000 : ℝ)*x 0 + (2495125233/5000000000 : ℝ)*x 1 + (178740363/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139005271/10000000000 : ℝ)^8229 ≤ (3207935431053/25000000000000 : ℝ)^6181 := by
    have hnat : (2139005271 : ℕ)^8229*25000000000000^6181 ≤ 3207935431053^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139005271 10000000000 3207935431053 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2495125233/5000000000 : ℝ)^8229 ≤ (39636820848573/100000000000000 : ℝ)^6181 := by
    have hnat : (2495125233 : ℕ)^8229*100000000000000^6181 ≤ 39636820848573^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495125233 5000000000 39636820848573 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (178740363/312500000 : ℝ)^8229 ≤ (118828593513/250000000000 : ℝ)^6181 := by
    have hnat : (178740363 : ℕ)^8229*250000000000^6181 ≤ 118828593513^6181*312500000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178740363 312500000 118828593513 250000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139005271/10000000000 : ℝ), (2495125233/5000000000 : ℝ), (178740363/312500000 : ℝ)] ![(3207935431053/25000000000000 : ℝ), (39636820848573/100000000000000 : ℝ), (118828593513/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139005271/10000000000 : ℝ)|^8229 ≤ (3207935431053/25000000000000 : ℝ)^6181
        have hw : |(-2139005271/10000000000 : ℝ)|=(2139005271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2495125233/5000000000 : ℝ)|^8229 ≤ (39636820848573/100000000000000 : ℝ)^6181
        have hw : |(2495125233/5000000000 : ℝ)|=(2495125233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(178740363/312500000 : ℝ)|^8229 ≤ (118828593513/250000000000 : ℝ)^6181
        have hw : |(178740363/312500000 : ℝ)|=(178740363/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s1_5 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2616736793/5000000000 : ℝ)*x 0 + (-1805455139/10000000000 : ℝ)*x 1 + (5719692671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2616736793/5000000000 : ℝ)^8229 ≤ (329916873639/781250000000 : ℝ)^6181 := by
    have hnat : (2616736793 : ℕ)^8229*781250000000^6181 ≤ 329916873639^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616736793 5000000000 329916873639 781250000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1805455139/10000000000 : ℝ)^8229 ≤ (1279898885179/12500000000000 : ℝ)^6181 := by
    have hnat : (1805455139 : ℕ)^8229*12500000000000^6181 ≤ 1279898885179^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805455139 10000000000 1279898885179 12500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5719692671/10000000000 : ℝ)^8229 ≤ (47531449077303/100000000000000 : ℝ)^6181 := by
    have hnat : (5719692671 : ℕ)^8229*100000000000000^6181 ≤ 47531449077303^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5719692671 10000000000 47531449077303 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2616736793/5000000000 : ℝ), (-1805455139/10000000000 : ℝ), (5719692671/10000000000 : ℝ)] ![(329916873639/781250000000 : ℝ), (1279898885179/12500000000000 : ℝ), (47531449077303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2616736793/5000000000 : ℝ)|^8229 ≤ (329916873639/781250000000 : ℝ)^6181
        have hw : |(2616736793/5000000000 : ℝ)|=(2616736793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1805455139/10000000000 : ℝ)|^8229 ≤ (1279898885179/12500000000000 : ℝ)^6181
        have hw : |(-1805455139/10000000000 : ℝ)|=(1805455139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5719692671/10000000000 : ℝ)|^8229 ≤ (47531449077303/100000000000000 : ℝ)^6181
        have hw : |(5719692671/10000000000 : ℝ)|=(5719692671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s1_6 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1046694347/2000000000 : ℝ)*x 0 + (5719694703/10000000000 : ℝ)*x 1 + (-451363699/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046694347/2000000000 : ℝ)^8229 ≤ (21114669970543/50000000000000 : ℝ)^6181 := by
    have hnat : (1046694347 : ℕ)^8229*50000000000000^6181 ≤ 21114669970543^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046694347 2000000000 21114669970543 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5719694703/10000000000 : ℝ)^8229 ≤ (47531471558551/100000000000000 : ℝ)^6181 := by
    have hnat : (5719694703 : ℕ)^8229*100000000000000^6181 ≤ 47531471558551^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5719694703 10000000000 47531471558551 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451363699/2500000000 : ℝ)^8229 ≤ (10239188491661/100000000000000 : ℝ)^6181 := by
    have hnat : (451363699 : ℕ)^8229*100000000000000^6181 ≤ 10239188491661^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451363699 2500000000 10239188491661 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046694347/2000000000 : ℝ), (5719694703/10000000000 : ℝ), (-451363699/2500000000 : ℝ)] ![(21114669970543/50000000000000 : ℝ), (47531471558551/100000000000000 : ℝ), (10239188491661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046694347/2000000000 : ℝ)|^8229 ≤ (21114669970543/50000000000000 : ℝ)^6181
        have hw : |(1046694347/2000000000 : ℝ)|=(1046694347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5719694703/10000000000 : ℝ)|^8229 ≤ (47531471558551/100000000000000 : ℝ)^6181
        have hw : |(5719694703/10000000000 : ℝ)|=(5719694703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-451363699/2500000000 : ℝ)|^8229 ≤ (10239188491661/100000000000000 : ℝ)^6181
        have hw : |(-451363699/2500000000 : ℝ)|=(451363699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s1_7 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4328232991/10000000000 : ℝ)*x 0 + (1274876839/2500000000 : ℝ)*x 1 + (367841551/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328232991/10000000000 : ℝ)^8229 ≤ (3279491679349/10000000000000 : ℝ)^6181 := by
    have hnat : (4328232991 : ℕ)^8229*10000000000000^6181 ≤ 3279491679349^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328232991 10000000000 3279491679349 10000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1274876839/2500000000 : ℝ)^8229 ≤ (10199085344107/25000000000000 : ℝ)^6181 := by
    have hnat : (1274876839 : ℕ)^8229*25000000000000^6181 ≤ 10199085344107^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274876839 2500000000 10199085344107 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (367841551/1000000000 : ℝ)^8229 ≤ (26408741823509/100000000000000 : ℝ)^6181 := by
    have hnat : (367841551 : ℕ)^8229*100000000000000^6181 ≤ 26408741823509^6181*1000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367841551 1000000000 26408741823509 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328232991/10000000000 : ℝ), (1274876839/2500000000 : ℝ), (367841551/1000000000 : ℝ)] ![(3279491679349/10000000000000 : ℝ), (10199085344107/25000000000000 : ℝ), (26408741823509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328232991/10000000000 : ℝ)|^8229 ≤ (3279491679349/10000000000000 : ℝ)^6181
        have hw : |(4328232991/10000000000 : ℝ)|=(4328232991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1274876839/2500000000 : ℝ)|^8229 ≤ (10199085344107/25000000000000 : ℝ)^6181
        have hw : |(1274876839/2500000000 : ℝ)|=(1274876839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(367841551/1000000000 : ℝ)|^8229 ≤ (26408741823509/100000000000000 : ℝ)^6181
        have hw : |(367841551/1000000000 : ℝ)|=(367841551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1036_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28227/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5041/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20931/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28227/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28227/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28227/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28227/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28227/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28227/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (0 : ℝ) ^ (2057/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2057 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2057*1^512 ≤ 0^512*1^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hpowhi : (28227/100000 : ℝ) ^ (2057/512 : ℝ) ≤ (310436381929421033/50000000000000000000 : ℝ) := by
    have hpowers : (28227/100000 : ℝ)^2057 ≤ (310436381929421033/50000000000000000000 : ℝ)^512 := by
      have hnat : (28227 : ℕ)^2057*50000000000000000000^512 ≤ 310436381929421033^512*100000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28227 100000 310436381929421033 50000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28227/100000 : ℝ)) (X := (310436381929421033/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2057 := by
      have hnat : (1 : ℕ)^512*1^2057 ≤ 1^2057*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50310436381929421033/50000000000000000000 : ℝ) ≤ (2503854500766429/2500000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (50310436381929421033/50000000000000000000 : ℝ)^512 ≤ (2503854500766429/2500000000000000 : ℝ)^2057 := by
      have hnat : (50310436381929421033 : ℕ)^512*2500000000000000^2057 ≤ 2503854500766429^2057*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50310436381929421033 50000000000000000000 2503854500766429 2500000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503854500766429/2500000000000000 : ℝ)) (X := (50310436381929421033/50000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25310436381929421033/25000000000000000000 : ℝ) ≤ (1253854500766429/1250000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (25310436381929421033/25000000000000000000 : ℝ)^512 ≤ (1253854500766429/1250000000000000 : ℝ)^2057 := by
      have hnat : (25310436381929421033 : ℕ)^512*1250000000000000^2057 ≤ 1253854500766429^2057*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25310436381929421033 25000000000000000000 1253854500766429 1250000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253854500766429/1250000000000000 : ℝ)) (X := (25310436381929421033/25000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3854500766429/705675000000000 : ℝ)*(0 : ℝ))^(2057/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(3854500766429/705675000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(310436381929421033/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3854500766429/705675000000000 : ℝ)*((28227/100000 : ℝ)+(0 : ℝ)))^(2057/512 : ℝ) := by
    rw [show (1 : ℝ)+(3854500766429/705675000000000 : ℝ)*((28227/100000 : ℝ)+(0 : ℝ))=(2503854500766429/2500000000000000 : ℝ) by norm_num, show 1+(310436381929421033/50000000000000000000 : ℝ)+(0 : ℝ)=(50310436381929421033/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(310436381929421033/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3854500766429/705675000000000 : ℝ)*(28227/100000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(3854500766429/705675000000000 : ℝ)*(28227/100000 : ℝ)=(1253854500766429/1250000000000000 : ℝ) by norm_num, show 1+2*(310436381929421033/50000000000000000000 : ℝ)=(25310436381929421033/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3854500766429/705675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (0 : ℝ)) (hi := (28227/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (3854500766429/705675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3854500766429/705675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (0 : ℝ)) (hi := (28227/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (3854500766429/705675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3854500766429/705675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (0 : ℝ)) (hi := (28227/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (3854500766429/705675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-267254613/1250000000 : ℝ)*X 0 0+(5730578977/10000000000 : ℝ)*X 0 1+(995916721/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2712486219/5000000000 : ℝ)*X 1 0+(-159097767/625000000 : ℝ)*X 1 1+(2489791961/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((271248639/500000000 : ℝ)*X 2 0+(4979583481/10000000000 : ℝ)*X 2 1+(-1272782191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2163174663/5000000000 : ℝ)*X 0 0+(3657207157/10000000000 : ℝ)*X 0 1+(5120291771/10000000000 : ℝ)*X 0 2+(2163174663/5000000000 : ℝ)*X 1 0+(3657207157/10000000000 : ℝ)*X 1 1+(5120291771/10000000000 : ℝ)*X 1 2+(2163174663/5000000000 : ℝ)*X 2 0+(3657207157/10000000000 : ℝ)*X 2 1+(5120291771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2139005271/10000000000 : ℝ)*X 0 0+(2495125233/5000000000 : ℝ)*X 0 1+(178740363/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2616736793/5000000000 : ℝ)*X 1 0+(-1805455139/10000000000 : ℝ)*X 1 1+(5719692671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1046694347/2000000000 : ℝ)*X 2 0+(5719694703/10000000000 : ℝ)*X 2 1+(-451363699/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4328232991/10000000000 : ℝ)*X 0 0+(1274876839/2500000000 : ℝ)*X 0 1+(367841551/1000000000 : ℝ)*X 0 2+(4328232991/10000000000 : ℝ)*X 1 0+(1274876839/2500000000 : ℝ)*X 1 1+(367841551/1000000000 : ℝ)*X 1 2+(4328232991/10000000000 : ℝ)*X 2 0+(1274876839/2500000000 : ℝ)*X 2 1+(367841551/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80943361962360362068389/23522500000000000000000000000 : ℝ) := by norm_num
    linear_combination (71721829/100000000000000 : ℝ)*(base1) + (798191621/100000000000000 : ℝ)*(base19) + (441068203/50000000000000 : ℝ)*(base23) + (46168377/50000000000000 : ℝ)*(upper3) + (78602841/100000000000000 : ℝ)*(upper5) + (1007532842648093/100000000000000 : ℝ)*(major0) + (1007532842648093/100000000000000 : ℝ)*(major1) + (1007532842648093/100000000000000 : ℝ)*(major2) + (1331570223072781/100000000000000 : ℝ)*(sp0) + (332893401935511/25000000000000 : ℝ)*(sp1) + (1331573523797259/100000000000000 : ℝ)*(sp2) + (170872295937281/25000000000000 : ℝ)*(sp3) + (4254582713/100000000000000 : ℝ)*(sp4) + (477297027/25000000000000 : ℝ)*(sp7) + (34174558232953/5000000000000 : ℝ)*(f.failure) + (266314881186733/20000000000000 : ℝ)*(f.sum) + (395431095938087/141135000000000000000000000000 : ℝ)*base66 + (838501841709691/141135000000000000000000000000 : ℝ)*base68 + (332840708395801/141135000000000000000000000000 : ℝ)*base70 + (68405013040973/70567500000000000000000000000 : ℝ)*base72 + (129660248745799/17641875000000000000000000000 : ℝ)*base74 + (230765695788113/70567500000000000000000000000 : ℝ)*base76 + (82506287080463/70567500000000000000000000000 : ℝ)*base78 + (272008432257031/141135000000000000000000000000 : ℝ)*base80 + (328139357023561/70567500000000000000000000000 : ℝ)*base82 + (179199/500000000000000000000 : ℝ)*base89 + (179199/500000000000000000000 : ℝ)*base91 + (179199/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27192203833328909977733/5880625000000000000000000000 : ℝ) := by norm_num
    linear_combination (2579430489/100000000000000 : ℝ)*(base19) + (2395246409/100000000000000 : ℝ)*(base23) + (148798127/100000000000000 : ℝ)*(upper2) + (357150161/100000000000000 : ℝ)*(upper3) + (100776069/20000000000000 : ℝ)*(upper5) + (518648877745763/50000000000000 : ℝ)*(major0) + (518648877745763/50000000000000 : ℝ)*(major1) + (518648877745763/50000000000000 : ℝ)*(major2) + (1505786487/12500000000000 : ℝ)*(sp1) + (12493411711/100000000000000 : ℝ)*(sp2) + (1370912240042503/100000000000000 : ℝ)*(sp4) + (685448807160059/50000000000000 : ℝ)*(sp5) + (21420271115381/1562500000000 : ℝ)*(sp6) + (21990097400191/3125000000000 : ℝ)*(sp7) + (21990097400191/3125000000000 : ℝ)*(f.failure) + (1370912240042503/100000000000000 : ℝ)*(f.sum) + (557412322346951/141135000000000000000000000000 : ℝ)*base65 + (398640303102571/70567500000000000000000000000 : ℝ)*base68 + (124685736764407/35283750000000000000000000000 : ℝ)*base69 + (41028755595491/17641875000000000000000000000 : ℝ)*base71 + (318790701656357/70567500000000000000000000000 : ℝ)*base74 + (83720988892021/70567500000000000000000000000 : ℝ)*base76 + (25026752862793/8820937500000000000000000000 : ℝ)*base77 + (1341173620568717/141135000000000000000000000000 : ℝ)*base80 + (264578111919163/70567500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (718553/312500000000000000000 : ℝ)*base89 + (718553/312500000000000000000 : ℝ)*base91 + (718553/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1036_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28227/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5041/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20931/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1036_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1036_s2_0 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098621107/5000000000 : ℝ)*x 0 + (345755783/625000000 : ℝ)*x 1 + (1028104787/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098621107/5000000000 : ℝ)^8229 ≤ (6649471186357/50000000000000 : ℝ)^6181 := by
    have hnat : (1098621107 : ℕ)^8229*50000000000000^6181 ≤ 6649471186357^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098621107 5000000000 6649471186357 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345755783/625000000 : ℝ)^8229 ≤ (22733638347367/50000000000000 : ℝ)^6181 := by
    have hnat : (345755783 : ℕ)^8229*50000000000000^6181 ≤ 22733638347367^6181*625000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345755783 625000000 22733638347367 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028104787/2000000000 : ℝ)^8229 ≤ (8246756183033/20000000000000 : ℝ)^6181 := by
    have hnat : (1028104787 : ℕ)^8229*20000000000000^6181 ≤ 8246756183033^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028104787 2000000000 8246756183033 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098621107/5000000000 : ℝ), (345755783/625000000 : ℝ), (1028104787/2000000000 : ℝ)] ![(6649471186357/50000000000000 : ℝ), (22733638347367/50000000000000 : ℝ), (8246756183033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098621107/5000000000 : ℝ)|^8229 ≤ (6649471186357/50000000000000 : ℝ)^6181
        have hw : |(-1098621107/5000000000 : ℝ)|=(1098621107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(345755783/625000000 : ℝ)|^8229 ≤ (22733638347367/50000000000000 : ℝ)^6181
        have hw : |(345755783/625000000 : ℝ)|=(345755783/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1028104787/2000000000 : ℝ)|^8229 ≤ (8246756183033/20000000000000 : ℝ)^6181
        have hw : |(1028104787/2000000000 : ℝ)|=(1028104787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s2_1 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2689265601/5000000000 : ℝ)*x 0 + (-2401709389/10000000000 : ℝ)*x 1 + (64256557/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689265601/5000000000 : ℝ)^8229 ≤ (10948694940413/25000000000000 : ℝ)^6181 := by
    have hnat : (2689265601 : ℕ)^8229*25000000000000^6181 ≤ 10948694940413^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689265601 5000000000 10948694940413 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2401709389/10000000000 : ℝ)^8229 ≤ (7485716317397/50000000000000 : ℝ)^6181 := by
    have hnat : (2401709389 : ℕ)^8229*50000000000000^6181 ≤ 7485716317397^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401709389 10000000000 7485716317397 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64256557/125000000 : ℝ)^8229 ≤ (20616893794797/50000000000000 : ℝ)^6181 := by
    have hnat : (64256557 : ℕ)^8229*50000000000000^6181 ≤ 20616893794797^6181*125000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64256557 125000000 20616893794797 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689265601/5000000000 : ℝ), (-2401709389/10000000000 : ℝ), (64256557/125000000 : ℝ)] ![(10948694940413/25000000000000 : ℝ), (7485716317397/50000000000000 : ℝ), (20616893794797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689265601/5000000000 : ℝ)|^8229 ≤ (10948694940413/25000000000000 : ℝ)^6181
        have hw : |(2689265601/5000000000 : ℝ)|=(2689265601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2401709389/10000000000 : ℝ)|^8229 ≤ (7485716317397/50000000000000 : ℝ)^6181
        have hw : |(-2401709389/10000000000 : ℝ)|=(2401709389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(64256557/125000000 : ℝ)|^8229 ≤ (20616893794797/50000000000000 : ℝ)^6181
        have hw : |(64256557/125000000 : ℝ)|=(64256557/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s2_2 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (215141253/400000000 : ℝ)*x 0 + (642565569/1250000000 : ℝ)*x 1 + (-1200854619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215141253/400000000 : ℝ)^8229 ≤ (21897390547513/50000000000000 : ℝ)^6181 := by
    have hnat : (215141253 : ℕ)^8229*50000000000000^6181 ≤ 21897390547513^6181*400000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215141253 400000000 21897390547513 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642565569/1250000000 : ℝ)^8229 ≤ (41233787504161/100000000000000 : ℝ)^6181 := by
    have hnat : (642565569 : ℕ)^8229*100000000000000^6181 ≤ 41233787504161^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642565569 1250000000 41233787504161 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200854619/5000000000 : ℝ)^8229 ≤ (14971431381629/100000000000000 : ℝ)^6181 := by
    have hnat : (1200854619 : ℕ)^8229*100000000000000^6181 ≤ 14971431381629^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200854619 5000000000 14971431381629 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215141253/400000000 : ℝ), (642565569/1250000000 : ℝ), (-1200854619/5000000000 : ℝ)] ![(21897390547513/50000000000000 : ℝ), (41233787504161/100000000000000 : ℝ), (14971431381629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215141253/400000000 : ℝ)|^8229 ≤ (21897390547513/50000000000000 : ℝ)^6181
        have hw : |(215141253/400000000 : ℝ)|=(215141253/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642565569/1250000000 : ℝ)|^8229 ≤ (41233787504161/100000000000000 : ℝ)^6181
        have hw : |(642565569/1250000000 : ℝ)|=(642565569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1200854619/5000000000 : ℝ)|^8229 ≤ (14971431381629/100000000000000 : ℝ)^6181
        have hw : |(-1200854619/5000000000 : ℝ)|=(1200854619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s2_3 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (27290933/62500000 : ℝ)*x 0 + (160081667/400000000 : ℝ)*x 1 + (952978329/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27290933/62500000 : ℝ)^8229 ≤ (33181998711303/100000000000000 : ℝ)^6181 := by
    have hnat : (27290933 : ℕ)^8229*100000000000000^6181 ≤ 33181998711303^6181*62500000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27290933 62500000 33181998711303 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160081667/400000000 : ℝ)^8229 ≤ (7386563063113/25000000000000 : ℝ)^6181 := by
    have hnat : (160081667 : ℕ)^8229*25000000000000^6181 ≤ 7386563063113^6181*400000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160081667 400000000 7386563063113 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (952978329/2000000000 : ℝ)^8229 ≤ (3727174901411/10000000000000 : ℝ)^6181 := by
    have hnat : (952978329 : ℕ)^8229*10000000000000^6181 ≤ 3727174901411^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952978329 2000000000 3727174901411 10000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27290933/62500000 : ℝ), (160081667/400000000 : ℝ), (952978329/2000000000 : ℝ)] ![(33181998711303/100000000000000 : ℝ), (7386563063113/25000000000000 : ℝ), (3727174901411/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27290933/62500000 : ℝ)|^8229 ≤ (33181998711303/100000000000000 : ℝ)^6181
        have hw : |(27290933/62500000 : ℝ)|=(27290933/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160081667/400000000 : ℝ)|^8229 ≤ (7386563063113/25000000000000 : ℝ)^6181
        have hw : |(160081667/400000000 : ℝ)|=(160081667/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(952978329/2000000000 : ℝ)|^8229 ≤ (3727174901411/10000000000000 : ℝ)^6181
        have hw : |(952978329/2000000000 : ℝ)|=(952978329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s2_4 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098689193/5000000000 : ℝ)*x 0 + (5143431927/10000000000 : ℝ)*x 1 + (552915361/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098689193/5000000000 : ℝ)^8229 ≤ (532001586341/4000000000000 : ℝ)^6181 := by
    have hnat : (1098689193 : ℕ)^8229*4000000000000^6181 ≤ 532001586341^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098689193 5000000000 532001586341 4000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143431927/10000000000 : ℝ)^8229 ≤ (20632419261227/50000000000000 : ℝ)^6181 := by
    have hnat : (5143431927 : ℕ)^8229*50000000000000^6181 ≤ 20632419261227^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143431927 10000000000 20632419261227 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552915361/1000000000 : ℝ)^8229 ≤ (45435121801969/100000000000000 : ℝ)^6181 := by
    have hnat : (552915361 : ℕ)^8229*100000000000000^6181 ≤ 45435121801969^6181*1000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552915361 1000000000 45435121801969 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098689193/5000000000 : ℝ), (5143431927/10000000000 : ℝ), (552915361/1000000000 : ℝ)] ![(532001586341/4000000000000 : ℝ), (20632419261227/50000000000000 : ℝ), (45435121801969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098689193/5000000000 : ℝ)|^8229 ≤ (532001586341/4000000000000 : ℝ)^6181
        have hw : |(-1098689193/5000000000 : ℝ)|=(1098689193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143431927/10000000000 : ℝ)|^8229 ≤ (20632419261227/50000000000000 : ℝ)^6181
        have hw : |(5143431927/10000000000 : ℝ)|=(5143431927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(552915361/1000000000 : ℝ)|^8229 ≤ (45435121801969/100000000000000 : ℝ)^6181
        have hw : |(552915361/1000000000 : ℝ)|=(552915361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s2_5 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (527990661/1000000000 : ℝ)*x 0 + (-2013080423/10000000000 : ℝ)*x 1 + (43196513/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527990661/1000000000 : ℝ)^8229 ≤ (41727448099/97656250000 : ℝ)^6181 := by
    have hnat : (527990661 : ℕ)^8229*97656250000^6181 ≤ 41727448099^6181*1000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527990661 1000000000 41727448099 97656250000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2013080423/10000000000 : ℝ)^8229 ≤ (1479496343003/12500000000000 : ℝ)^6181 := by
    have hnat : (2013080423 : ℕ)^8229*12500000000000^6181 ≤ 1479496343003^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013080423 10000000000 1479496343003 12500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43196513/78125000 : ℝ)^8229 ≤ (22717561196367/50000000000000 : ℝ)^6181 := by
    have hnat : (43196513 : ℕ)^8229*50000000000000^6181 ≤ 22717561196367^6181*78125000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43196513 78125000 22717561196367 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527990661/1000000000 : ℝ), (-2013080423/10000000000 : ℝ), (43196513/78125000 : ℝ)] ![(41727448099/97656250000 : ℝ), (1479496343003/12500000000000 : ℝ), (22717561196367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527990661/1000000000 : ℝ)|^8229 ≤ (41727448099/97656250000 : ℝ)^6181
        have hw : |(527990661/1000000000 : ℝ)|=(527990661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2013080423/10000000000 : ℝ)|^8229 ≤ (1479496343003/12500000000000 : ℝ)^6181
        have hw : |(-2013080423/10000000000 : ℝ)|=(2013080423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43196513/78125000 : ℝ)|^8229 ≤ (22717561196367/50000000000000 : ℝ)^6181
        have hw : |(43196513/78125000 : ℝ)|=(43196513/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s2_6 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1319976703/2500000000 : ℝ)*x 0 + (2764576757/5000000000 : ℝ)*x 1 + (-2013080353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319976703/2500000000 : ℝ)^8229 ≤ (42728909029759/100000000000000 : ℝ)^6181 := by
    have hnat : (1319976703 : ℕ)^8229*100000000000000^6181 ≤ 42728909029759^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319976703 2500000000 42728909029759 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2764576757/5000000000 : ℝ)^8229 ≤ (45435120751719/100000000000000 : ℝ)^6181 := by
    have hnat : (2764576757 : ℕ)^8229*100000000000000^6181 ≤ 45435120751719^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2764576757 5000000000 45435120751719 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013080353/10000000000 : ℝ)^8229 ≤ (11835970196089/100000000000000 : ℝ)^6181 := by
    have hnat : (2013080353 : ℕ)^8229*100000000000000^6181 ≤ 11835970196089^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013080353 10000000000 11835970196089 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319976703/2500000000 : ℝ), (2764576757/5000000000 : ℝ), (-2013080353/10000000000 : ℝ)] ![(42728909029759/100000000000000 : ℝ), (45435120751719/100000000000000 : ℝ), (11835970196089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319976703/2500000000 : ℝ)|^8229 ≤ (42728909029759/100000000000000 : ℝ)^6181
        have hw : |(1319976703/2500000000 : ℝ)|=(1319976703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2764576757/5000000000 : ℝ)|^8229 ≤ (45435120751719/100000000000000 : ℝ)^6181
        have hw : |(2764576757/5000000000 : ℝ)|=(2764576757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2013080353/10000000000 : ℝ)|^8229 ≤ (11835970196089/100000000000000 : ℝ)^6181
        have hw : |(-2013080353/10000000000 : ℝ)|=(2013080353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s2_7 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1091703791/2500000000 : ℝ)*x 0 + (2379613883/5000000000 : ℝ)*x 1 + (500970801/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091703791/2500000000 : ℝ)^8229 ≤ (829617217287/2500000000000 : ℝ)^6181 := by
    have hnat : (1091703791 : ℕ)^8229*2500000000000^6181 ≤ 829617217287^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091703791 2500000000 829617217287 2500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2379613883/5000000000 : ℝ)^8229 ≤ (37212777337603/100000000000000 : ℝ)^6181 := by
    have hnat : (2379613883 : ℕ)^8229*100000000000000^6181 ≤ 37212777337603^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2379613883 5000000000 37212777337603 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500970801/1250000000 : ℝ)^8229 ≤ (29602533954693/100000000000000 : ℝ)^6181 := by
    have hnat : (500970801 : ℕ)^8229*100000000000000^6181 ≤ 29602533954693^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500970801 1250000000 29602533954693 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091703791/2500000000 : ℝ), (2379613883/5000000000 : ℝ), (500970801/1250000000 : ℝ)] ![(829617217287/2500000000000 : ℝ), (37212777337603/100000000000000 : ℝ), (29602533954693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091703791/2500000000 : ℝ)|^8229 ≤ (829617217287/2500000000000 : ℝ)^6181
        have hw : |(1091703791/2500000000 : ℝ)|=(1091703791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2379613883/5000000000 : ℝ)|^8229 ≤ (37212777337603/100000000000000 : ℝ)^6181
        have hw : |(2379613883/5000000000 : ℝ)|=(2379613883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(500970801/1250000000 : ℝ)|^8229 ≤ (29602533954693/100000000000000 : ℝ)^6181
        have hw : |(500970801/1250000000 : ℝ)|=(500970801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1036_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20931/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1713/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16839/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20931/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5041/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20931/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5041/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20931/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5041/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20931/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5041/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20931/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5041/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20931/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5041/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5041/100000 : ℝ) ^ (2057/512 : ℝ) ≤ (30635817265657/5000000000000000000 : ℝ) := by
    have hpowers : (5041/100000 : ℝ)^2057 ≤ (30635817265657/5000000000000000000 : ℝ)^512 := by
      have hnat : (5041 : ℕ)^2057*5000000000000000000^512 ≤ 30635817265657^512*100000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5041 100000 30635817265657 5000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5041/100000 : ℝ)) (X := (30635817265657/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hpowhi : (20931/100000 : ℝ) ^ (2057/512 : ℝ) ≤ (93366413491160029/50000000000000000000 : ℝ) := by
    have hpowers : (20931/100000 : ℝ)^2057 ≤ (93366413491160029/50000000000000000000 : ℝ)^512 := by
      have hnat : (20931 : ℕ)^2057*50000000000000000000^512 ≤ 93366413491160029^512*100000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20931 100000 93366413491160029 50000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20931/100000 : ℝ)) (X := (93366413491160029/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500030635817265657/2500000000000000000 : ℝ) ≤ (10000030501635887/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (2500030635817265657/2500000000000000000 : ℝ)^512 ≤ (10000030501635887/10000000000000000 : ℝ)^2057 := by
      have hnat : (2500030635817265657 : ℕ)^512*10000000000000000^2057 ≤ 10000030501635887^2057*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500030635817265657 2500000000000000000 10000030501635887 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000030501635887/10000000000000000 : ℝ)) (X := (2500030635817265657/2500000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50093672771663816599/50000000000000000000 : ℝ) ≤ (10004659868972723/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (50093672771663816599/50000000000000000000 : ℝ)^512 ≤ (10004659868972723/10000000000000000 : ℝ)^2057 := by
      have hnat : (50093672771663816599 : ℕ)^512*10000000000000000^2057 ≤ 10004659868972723^2057*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50093672771663816599 50000000000000000000 10004659868972723 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004659868972723/10000000000000000 : ℝ)) (X := (50093672771663816599/50000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25093366413491160029/25000000000000000000 : ℝ) ≤ (10009289236309559/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (25093366413491160029/25000000000000000000 : ℝ)^512 ≤ (10009289236309559/10000000000000000 : ℝ)^2057 := by
      have hnat : (25093366413491160029 : ℕ)^512*10000000000000000^2057 ≤ 10009289236309559^2057*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25093366413491160029 25000000000000000000 10009289236309559 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009289236309559/10000000000000000 : ℝ)) (X := (25093366413491160029/25000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(30635817265657/5000000000000000000 : ℝ) ≤ ((79426905694752131939/79450000000000000000 : ℝ)+2*(1157341834209/397250000000000 : ℝ)*(5041/100000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (79426905694752131939/79450000000000000000 : ℝ)+2*(1157341834209/397250000000000 : ℝ)*(5041/100000 : ℝ)=(10000030501635887/10000000000000000 : ℝ) by norm_num, show 1+2*(30635817265657/5000000000000000000 : ℝ)=(2500030635817265657/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(93366413491160029/50000000000000000000 : ℝ)+(30635817265657/5000000000000000000 : ℝ) ≤ ((79426905694752131939/79450000000000000000 : ℝ)+(1157341834209/397250000000000 : ℝ)*((20931/100000 : ℝ)+(5041/100000 : ℝ)))^(2057/512 : ℝ) := by
    rw [show (79426905694752131939/79450000000000000000 : ℝ)+(1157341834209/397250000000000 : ℝ)*((20931/100000 : ℝ)+(5041/100000 : ℝ))=(10004659868972723/10000000000000000 : ℝ) by norm_num, show 1+(93366413491160029/50000000000000000000 : ℝ)+(30635817265657/5000000000000000000 : ℝ)=(50093672771663816599/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(93366413491160029/50000000000000000000 : ℝ) ≤ ((79426905694752131939/79450000000000000000 : ℝ)+2*(1157341834209/397250000000000 : ℝ)*(20931/100000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (79426905694752131939/79450000000000000000 : ℝ)+2*(1157341834209/397250000000000 : ℝ)*(20931/100000 : ℝ)=(10009289236309559/10000000000000000 : ℝ) by norm_num, show 1+2*(93366413491160029/50000000000000000000 : ℝ)=(25093366413491160029/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (79426905694752131939/79450000000000000000 : ℝ)*(X 1 0+X 2 0)+(1157341834209/397250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (5041/100000 : ℝ)) (hi := (20931/100000 : ℝ)) (c := (79426905694752131939/79450000000000000000 : ℝ)) (alpha := (1157341834209/397250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (79426905694752131939/79450000000000000000 : ℝ)*(X 0 1+X 2 1)+(1157341834209/397250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (5041/100000 : ℝ)) (hi := (20931/100000 : ℝ)) (c := (79426905694752131939/79450000000000000000 : ℝ)) (alpha := (1157341834209/397250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (79426905694752131939/79450000000000000000 : ℝ)*(X 0 2+X 1 2)+(1157341834209/397250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (5041/100000 : ℝ)) (hi := (20931/100000 : ℝ)) (c := (79426905694752131939/79450000000000000000 : ℝ)) (alpha := (1157341834209/397250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1098621107/5000000000 : ℝ)*X 0 0+(345755783/625000000 : ℝ)*X 0 1+(1028104787/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2689265601/5000000000 : ℝ)*X 1 0+(-2401709389/10000000000 : ℝ)*X 1 1+(64256557/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((215141253/400000000 : ℝ)*X 2 0+(642565569/1250000000 : ℝ)*X 2 1+(-1200854619/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((27290933/62500000 : ℝ)*X 0 0+(160081667/400000000 : ℝ)*X 0 1+(952978329/2000000000 : ℝ)*X 0 2+(27290933/62500000 : ℝ)*X 1 0+(160081667/400000000 : ℝ)*X 1 1+(952978329/2000000000 : ℝ)*X 1 2+(27290933/62500000 : ℝ)*X 2 0+(160081667/400000000 : ℝ)*X 2 1+(952978329/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1098689193/5000000000 : ℝ)*X 0 0+(5143431927/10000000000 : ℝ)*X 0 1+(552915361/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((527990661/1000000000 : ℝ)*X 1 0+(-2013080423/10000000000 : ℝ)*X 1 1+(43196513/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319976703/2500000000 : ℝ)*X 2 0+(2764576757/5000000000 : ℝ)*X 2 1+(-2013080353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1091703791/2500000000 : ℝ)*X 0 0+(2379613883/5000000000 : ℝ)*X 0 1+(500970801/1250000000 : ℝ)*X 0 2+(1091703791/2500000000 : ℝ)*X 1 0+(2379613883/5000000000 : ℝ)*X 1 1+(500970801/1250000000 : ℝ)*X 1 2+(1091703791/2500000000 : ℝ)*X 2 0+(2379613883/5000000000 : ℝ)*X 2 1+(500970801/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76716419202178593517161/39725000000000000000000000000 : ℝ) := by norm_num
    linear_combination (851432323/100000000000000 : ℝ)*(base19) + (151676943/20000000000000 : ℝ)*(base23) + (62060713/50000000000000 : ℝ)*(upper3) + (81458331/100000000000000 : ℝ)*(upper4) + (2128473/2000000000000 : ℝ)*(upper5) + (1932367255253359/100000000000000 : ℝ)*(major0) + (1932367255253359/100000000000000 : ℝ)*(major1) + (1932367255253359/100000000000000 : ℝ)*(major2) + (2553841602988769/100000000000000 : ℝ)*(sp0) + (127692615564877/5000000000000 : ℝ)*(sp1) + (638463101086287/25000000000000 : ℝ)*(sp2) + (1310877263851083/100000000000000 : ℝ)*(sp3) + (5779870547/50000000000000 : ℝ)*(sp4) + (803910571/20000000000000 : ℝ)*(sp7) + (655440641701969/50000000000000 : ℝ)*(f.failure) + (2553853162729863/100000000000000 : ℝ)*(f.sum) + (40972906791547/9931250000000000000000000000 : ℝ)*base66 + (42494623348677866899/7945000000000000000000000000000000 : ℝ)*base68 + (44429638539597133101/7945000000000000000000000000000000 : ℝ)*base69 + (20280597325852866899/7945000000000000000000000000000000 : ℝ)*base72 + (175879769537813/39725000000000000000000000000 : ℝ)*base74 + (7076641767072133101/7945000000000000000000000000000000 : ℝ)*base75 + (9427075994752866899/7945000000000000000000000000000000 : ℝ)*base78 + (16379832557252133101/7945000000000000000000000000000000 : ℝ)*base79 + (99078158442587/39725000000000000000000000000 : ℝ)*base81 + (50962727/5000000000000000000000 : ℝ)*base89 + (50962727/5000000000000000000000 : ℝ)*base91 + (50962727/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26259399988114233090737631477/3972500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (251168853/20000000000000 : ℝ)*(base19) + (179743659/12500000000000 : ℝ)*(base23) + (82224591/50000000000000 : ℝ)*(upper3) + (30504073/100000000000000 : ℝ)*(lower4) + (76638687/50000000000000 : ℝ)*(upper5) + (1961641827244019/100000000000000 : ℝ)*(major0) + (1961641827244019/100000000000000 : ℝ)*(major1) + (1961641827244019/100000000000000 : ℝ)*(major2) + (5288065389/50000000000000 : ℝ)*(sp1) + (5961144371/50000000000000 : ℝ)*(sp2) + (648135709131299/25000000000000 : ℝ)*(sp4) + (324066375568769/12500000000000 : ℝ)*(sp5) + (2592529476287181/100000000000000 : ℝ)*(sp6) + (1330740597619643/100000000000000 : ℝ)*(sp7) + (1330740597619643/100000000000000 : ℝ)*(f.failure) + (648135709131299/25000000000000 : ℝ)*(f.sum) + (29264083685421/19862500000000000000000000000 : ℝ)*base65 + (20160741425119177159/7945000000000000000000000000000000 : ℝ)*base68 + (8250150985049177159/7945000000000000000000000000000000 : ℝ)*base70 + (40151611926270822841/7945000000000000000000000000000000 : ℝ)*base71 + (18870814096529/19862500000000000000000000000 : ℝ)*base74 + (68307018518590822841/7945000000000000000000000000000000 : ℝ)*base75 + (36614654871800822841/7945000000000000000000000000000000 : ℝ)*base77 + (91568483237810822841/7945000000000000000000000000000000 : ℝ)*base79 + (117566642322933/39725000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8832531/10000000000000000000000 : ℝ)*base90 + (8832531/10000000000000000000000 : ℝ)*base92 + (8832531/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1036_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20931/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1713/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16839/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1036_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1036_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1713/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16839/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1036_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1036_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1036_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1713/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16839/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1036_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
