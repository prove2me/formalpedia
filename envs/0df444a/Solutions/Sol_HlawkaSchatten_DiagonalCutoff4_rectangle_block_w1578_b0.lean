-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1578_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:29:49.289206+00:00
-- url     : https://prove2.me/submissions/8dd8956b-a4f5-4860-b062-5b139f1ed8af

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
theorem support_rectangle_w1578_s0_0 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1618015117/10000000000 : ℝ)*x 0 + (146594699/250000000 : ℝ)*x 1 + (4882546287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1618015117/10000000000 : ℝ)^4653 ≤ (4838938329873/50000000000000 : ℝ)^3629 := by
    have hnat : (1618015117 : ℕ)^4653*50000000000000^3629 ≤ 4838938329873^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1618015117 10000000000 4838938329873 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146594699/250000000 : ℝ)^4653 ≤ (50438805437411/100000000000000 : ℝ)^3629 := by
    have hnat : (146594699 : ℕ)^4653*100000000000000^3629 ≤ 50438805437411^3629*250000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146594699 250000000 50438805437411 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4882546287/10000000000 : ℝ)^4653 ≤ (155794210529/390625000000 : ℝ)^3629 := by
    have hnat : (4882546287 : ℕ)^4653*390625000000^3629 ≤ 155794210529^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4882546287 10000000000 155794210529 390625000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1618015117/10000000000 : ℝ), (146594699/250000000 : ℝ), (4882546287/10000000000 : ℝ)] ![(4838938329873/50000000000000 : ℝ), (50438805437411/100000000000000 : ℝ), (155794210529/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1618015117/10000000000 : ℝ)|^4653 ≤ (4838938329873/50000000000000 : ℝ)^3629
        have hw : |(-1618015117/10000000000 : ℝ)|=(1618015117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(146594699/250000000 : ℝ)|^4653 ≤ (50438805437411/100000000000000 : ℝ)^3629
        have hw : |(146594699/250000000 : ℝ)|=(146594699/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4882546287/10000000000 : ℝ)|^4653 ≤ (155794210529/390625000000 : ℝ)^3629
        have hw : |(4882546287/10000000000 : ℝ)|=(4882546287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s0_1 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5463774493/10000000000 : ℝ)*x 0 + (-2163532239/10000000000 : ℝ)*x 1 + (4882546267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5463774493/10000000000 : ℝ)^4653 ≤ (11517566863633/25000000000000 : ℝ)^3629 := by
    have hnat : (5463774493 : ℕ)^4653*25000000000000^3629 ≤ 11517566863633^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463774493 10000000000 11517566863633 25000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2163532239/10000000000 : ℝ)^4653 ≤ (14046414843657/100000000000000 : ℝ)^3629 := by
    have hnat : (2163532239 : ℕ)^4653*100000000000000^3629 ≤ 14046414843657^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163532239 10000000000 14046414843657 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4882546267/10000000000 : ℝ)^4653 ≤ (7976663537191/20000000000000 : ℝ)^3629 := by
    have hnat : (4882546267 : ℕ)^4653*20000000000000^3629 ≤ 7976663537191^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4882546267 10000000000 7976663537191 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5463774493/10000000000 : ℝ), (-2163532239/10000000000 : ℝ), (4882546267/10000000000 : ℝ)] ![(11517566863633/25000000000000 : ℝ), (14046414843657/100000000000000 : ℝ), (7976663537191/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5463774493/10000000000 : ℝ)|^4653 ≤ (11517566863633/25000000000000 : ℝ)^3629
        have hw : |(5463774493/10000000000 : ℝ)|=(5463774493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2163532239/10000000000 : ℝ)|^4653 ≤ (14046414843657/100000000000000 : ℝ)^3629
        have hw : |(-2163532239/10000000000 : ℝ)|=(2163532239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4882546267/10000000000 : ℝ)|^4653 ≤ (7976663537191/20000000000000 : ℝ)^3629
        have hw : |(4882546267/10000000000 : ℝ)|=(4882546267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s0_2 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5463774557/10000000000 : ℝ)*x 0 + (4882546183/10000000000 : ℝ)*x 1 + (-1081766131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5463774557/10000000000 : ℝ)^4653 ≤ (46070268146449/100000000000000 : ℝ)^3629 := by
    have hnat : (5463774557 : ℕ)^4653*100000000000000^3629 ≤ 46070268146449^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463774557 10000000000 46070268146449 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4882546183/10000000000 : ℝ)^4653 ≤ (39883316806183/100000000000000 : ℝ)^3629 := by
    have hnat : (4882546183 : ℕ)^4653*100000000000000^3629 ≤ 39883316806183^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4882546183 10000000000 39883316806183 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081766131/5000000000 : ℝ)^4653 ≤ (3511603758779/25000000000000 : ℝ)^3629 := by
    have hnat : (1081766131 : ℕ)^4653*25000000000000^3629 ≤ 3511603758779^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081766131 5000000000 3511603758779 25000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5463774557/10000000000 : ℝ), (4882546183/10000000000 : ℝ), (-1081766131/5000000000 : ℝ)] ![(46070268146449/100000000000000 : ℝ), (39883316806183/100000000000000 : ℝ), (3511603758779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5463774557/10000000000 : ℝ)|^4653 ≤ (46070268146449/100000000000000 : ℝ)^3629
        have hw : |(5463774557/10000000000 : ℝ)|=(5463774557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4882546183/10000000000 : ℝ)|^4653 ≤ (39883316806183/100000000000000 : ℝ)^3629
        have hw : |(4882546183/10000000000 : ℝ)|=(4882546183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1081766131/5000000000 : ℝ)|^4653 ≤ (3511603758779/25000000000000 : ℝ)^3629
        have hw : |(-1081766131/5000000000 : ℝ)|=(1081766131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s0_3 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2063896159/5000000000 : ℝ)*x 0 + (1546814837/5000000000 : ℝ)*x 1 + (2711270139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063896159/5000000000 : ℝ)^4653 ≤ (16078828701863/50000000000000 : ℝ)^3629 := by
    have hnat : (2063896159 : ℕ)^4653*50000000000000^3629 ≤ 16078828701863^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063896159 5000000000 16078828701863 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1546814837/5000000000 : ℝ)^4653 ≤ (2221739110313/10000000000000 : ℝ)^3629 := by
    have hnat : (1546814837 : ℕ)^4653*10000000000000^3629 ≤ 2221739110313^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1546814837 5000000000 2221739110313 10000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711270139/5000000000 : ℝ)^4653 ≤ (5703118934027/12500000000000 : ℝ)^3629 := by
    have hnat : (2711270139 : ℕ)^4653*12500000000000^3629 ≤ 5703118934027^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711270139 5000000000 5703118934027 12500000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2063896159/5000000000 : ℝ), (1546814837/5000000000 : ℝ), (2711270139/5000000000 : ℝ)] ![(16078828701863/50000000000000 : ℝ), (2221739110313/10000000000000 : ℝ), (5703118934027/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2063896159/5000000000 : ℝ)|^4653 ≤ (16078828701863/50000000000000 : ℝ)^3629
        have hw : |(2063896159/5000000000 : ℝ)|=(2063896159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1546814837/5000000000 : ℝ)|^4653 ≤ (2221739110313/10000000000000 : ℝ)^3629
        have hw : |(1546814837/5000000000 : ℝ)|=(1546814837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711270139/5000000000 : ℝ)|^4653 ≤ (5703118934027/12500000000000 : ℝ)^3629
        have hw : |(2711270139/5000000000 : ℝ)|=(2711270139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s0_4 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-810505447/5000000000 : ℝ)*x 0 + (245361473/500000000 : ℝ)*x 1 + (2919115871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (810505447/5000000000 : ℝ)^4653 ≤ (9700857529261/100000000000000 : ℝ)^3629 := by
    have hnat : (810505447 : ℕ)^4653*100000000000000^3629 ≤ 9700857529261^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810505447 5000000000 9700857529261 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245361473/500000000 : ℝ)^4653 ≤ (40142020770939/100000000000000 : ℝ)^3629 := by
    have hnat : (245361473 : ℕ)^4653*100000000000000^3629 ≤ 40142020770939^3629*500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245361473 500000000 40142020770939 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2919115871/5000000000 : ℝ)^4653 ≤ (501571216857/1000000000000 : ℝ)^3629 := by
    have hnat : (2919115871 : ℕ)^4653*1000000000000^3629 ≤ 501571216857^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2919115871 5000000000 501571216857 1000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-810505447/5000000000 : ℝ), (245361473/500000000 : ℝ), (2919115871/5000000000 : ℝ)] ![(9700857529261/100000000000000 : ℝ), (40142020770939/100000000000000 : ℝ), (501571216857/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-810505447/5000000000 : ℝ)|^4653 ≤ (9700857529261/100000000000000 : ℝ)^3629
        have hw : |(-810505447/5000000000 : ℝ)|=(810505447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(245361473/500000000 : ℝ)|^4653 ≤ (40142020770939/100000000000000 : ℝ)^3629
        have hw : |(245361473/500000000 : ℝ)|=(245361473/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2919115871/5000000000 : ℝ)|^4653 ≤ (501571216857/1000000000000 : ℝ)^3629
        have hw : |(2919115871/5000000000 : ℝ)|=(2919115871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s0_5 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597759087/5000000000 : ℝ)*x 0 + (-603923631/5000000000 : ℝ)*x 1 + (729778937/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597759087/5000000000 : ℝ)^4653 ≤ (21595212063827/50000000000000 : ℝ)^3629 := by
    have hnat : (2597759087 : ℕ)^4653*50000000000000^3629 ≤ 21595212063827^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597759087 5000000000 21595212063827 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603923631/5000000000 : ℝ)^4653 ≤ (3326228439203/50000000000000 : ℝ)^3629 := by
    have hnat : (603923631 : ℕ)^4653*50000000000000^3629 ≤ 3326228439203^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603923631 5000000000 3326228439203 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (729778937/1250000000 : ℝ)^4653 ≤ (5015711897593/10000000000000 : ℝ)^3629 := by
    have hnat : (729778937 : ℕ)^4653*10000000000000^3629 ≤ 5015711897593^3629*1250000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729778937 1250000000 5015711897593 10000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597759087/5000000000 : ℝ), (-603923631/5000000000 : ℝ), (729778937/1250000000 : ℝ)] ![(21595212063827/50000000000000 : ℝ), (3326228439203/50000000000000 : ℝ), (5015711897593/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597759087/5000000000 : ℝ)|^4653 ≤ (21595212063827/50000000000000 : ℝ)^3629
        have hw : |(2597759087/5000000000 : ℝ)|=(2597759087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-603923631/5000000000 : ℝ)|^4653 ≤ (3326228439203/50000000000000 : ℝ)^3629
        have hw : |(-603923631/5000000000 : ℝ)|=(603923631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(729778937/1250000000 : ℝ)|^4653 ≤ (5015711897593/10000000000000 : ℝ)^3629
        have hw : |(729778937/1250000000 : ℝ)|=(729778937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s0_6 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597758569/5000000000 : ℝ)*x 0 + (5838232711/10000000000 : ℝ)*x 1 + (-120784693/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597758569/5000000000 : ℝ)^4653 ≤ (4319041308523/10000000000000 : ℝ)^3629 := by
    have hnat : (2597758569 : ℕ)^4653*10000000000000^3629 ≤ 4319041308523^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597758569 5000000000 4319041308523 10000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5838232711/10000000000 : ℝ)^4653 ≤ (50157132359551/100000000000000 : ℝ)^3629 := by
    have hnat : (5838232711 : ℕ)^4653*100000000000000^3629 ≤ 50157132359551^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5838232711 10000000000 50157132359551 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120784693/1000000000 : ℝ)^4653 ≤ (1330490906777/20000000000000 : ℝ)^3629 := by
    have hnat : (120784693 : ℕ)^4653*20000000000000^3629 ≤ 1330490906777^3629*1000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120784693 1000000000 1330490906777 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597758569/5000000000 : ℝ), (5838232711/10000000000 : ℝ), (-120784693/1000000000 : ℝ)] ![(4319041308523/10000000000000 : ℝ), (50157132359551/100000000000000 : ℝ), (1330490906777/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597758569/5000000000 : ℝ)|^4653 ≤ (4319041308523/10000000000000 : ℝ)^3629
        have hw : |(2597758569/5000000000 : ℝ)|=(2597758569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5838232711/10000000000 : ℝ)|^4653 ≤ (50157132359551/100000000000000 : ℝ)^3629
        have hw : |(5838232711/10000000000 : ℝ)|=(5838232711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-120784693/1000000000 : ℝ)|^4653 ≤ (1330490906777/20000000000000 : ℝ)^3629
        have hw : |(-120784693/1000000000 : ℝ)|=(120784693/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s0_7 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103372511/250000000 : ℝ)*x 0 + (1072790599/2000000000 : ℝ)*x 1 + (3154285297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103372511/250000000 : ℝ)^4653 ≤ (8057169036611/25000000000000 : ℝ)^3629 := by
    have hnat : (103372511 : ℕ)^4653*25000000000000^3629 ≤ 8057169036611^3629*250000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103372511 250000000 8057169036611 25000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072790599/2000000000 : ℝ)^4653 ≤ (44993870873317/100000000000000 : ℝ)^3629 := by
    have hnat : (1072790599 : ℕ)^4653*100000000000000^3629 ≤ 44993870873317^3629*2000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072790599 2000000000 44993870873317 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154285297/10000000000 : ℝ)^4653 ≤ (22777452973737/100000000000000 : ℝ)^3629 := by
    have hnat : (3154285297 : ℕ)^4653*100000000000000^3629 ≤ 22777452973737^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154285297 10000000000 22777452973737 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103372511/250000000 : ℝ), (1072790599/2000000000 : ℝ), (3154285297/10000000000 : ℝ)] ![(8057169036611/25000000000000 : ℝ), (44993870873317/100000000000000 : ℝ), (22777452973737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103372511/250000000 : ℝ)|^4653 ≤ (8057169036611/25000000000000 : ℝ)^3629
        have hw : |(103372511/250000000 : ℝ)|=(103372511/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1072790599/2000000000 : ℝ)|^4653 ≤ (44993870873317/100000000000000 : ℝ)^3629
        have hw : |(1072790599/2000000000 : ℝ)|=(1072790599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154285297/10000000000 : ℝ)|^4653 ≤ (22777452973737/100000000000000 : ℝ)^3629
        have hw : |(3154285297/10000000000 : ℝ)|=(3154285297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1578_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3639/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24657/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4651/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4651 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4651*1^1024 ≤ 0^1024*1^4651 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4651 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4651/1024 : ℝ) ≤ (1557971789375636181/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4651 ≤ (1557971789375636181/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4651*100000000000000000000^1024 ≤ 1557971789375636181^1024*5^4651 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1557971789375636181 100000000000000000000 4651 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1557971789375636181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4651 := by
      have hnat : (1 : ℕ)^1024*1^4651 ≤ 1^4651*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101557971789375636181/100000000000000000000 : ℝ) ≤ (2006819007729091/2000000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (101557971789375636181/100000000000000000000 : ℝ)^1024 ≤ (2006819007729091/2000000000000000 : ℝ)^4651 := by
      have hnat : (101557971789375636181 : ℕ)^1024*2000000000000000^4651 ≤ 2006819007729091^4651*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101557971789375636181 100000000000000000000 2006819007729091 2000000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2006819007729091/2000000000000000 : ℝ)) (X := (101557971789375636181/100000000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51557971789375636181/50000000000000000000 : ℝ) ≤ (1006819007729091/1000000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (51557971789375636181/50000000000000000000 : ℝ)^1024 ≤ (1006819007729091/1000000000000000 : ℝ)^4651 := by
      have hnat : (51557971789375636181 : ℕ)^1024*1000000000000000^4651 ≤ 1006819007729091^4651*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51557971789375636181 50000000000000000000 1006819007729091 1000000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1006819007729091/1000000000000000 : ℝ)) (X := (51557971789375636181/50000000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6819007729091/800000000000000 : ℝ)*(0 : ℝ))^(4651/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6819007729091/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1557971789375636181/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6819007729091/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4651/1024 : ℝ) := by
    rw [show (1 : ℝ)+(6819007729091/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2006819007729091/2000000000000000 : ℝ) by norm_num, show 1+(1557971789375636181/100000000000000000000 : ℝ)+(0 : ℝ)=(101557971789375636181/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1557971789375636181/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6819007729091/800000000000000 : ℝ)*(2/5 : ℝ))^(4651/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6819007729091/800000000000000 : ℝ)*(2/5 : ℝ)=(1006819007729091/1000000000000000 : ℝ) by norm_num, show 1+2*(1557971789375636181/100000000000000000000 : ℝ)=(51557971789375636181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6819007729091/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6819007729091/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6819007729091/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6819007729091/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6819007729091/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6819007729091/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1618015117/10000000000 : ℝ)*X 0 0+(146594699/250000000 : ℝ)*X 0 1+(4882546287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5463774493/10000000000 : ℝ)*X 1 0+(-2163532239/10000000000 : ℝ)*X 1 1+(4882546267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5463774557/10000000000 : ℝ)*X 2 0+(4882546183/10000000000 : ℝ)*X 2 1+(-1081766131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2063896159/5000000000 : ℝ)*X 0 0+(1546814837/5000000000 : ℝ)*X 0 1+(2711270139/5000000000 : ℝ)*X 0 2+(2063896159/5000000000 : ℝ)*X 1 0+(1546814837/5000000000 : ℝ)*X 1 1+(2711270139/5000000000 : ℝ)*X 1 2+(2063896159/5000000000 : ℝ)*X 2 0+(1546814837/5000000000 : ℝ)*X 2 1+(2711270139/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-810505447/5000000000 : ℝ)*X 0 0+(245361473/500000000 : ℝ)*X 0 1+(2919115871/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2597759087/5000000000 : ℝ)*X 1 0+(-603923631/5000000000 : ℝ)*X 1 1+(729778937/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2597758569/5000000000 : ℝ)*X 2 0+(5838232711/10000000000 : ℝ)*X 2 1+(-120784693/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((103372511/250000000 : ℝ)*X 0 0+(1072790599/2000000000 : ℝ)*X 0 1+(3154285297/10000000000 : ℝ)*X 0 2+(103372511/250000000 : ℝ)*X 1 0+(1072790599/2000000000 : ℝ)*X 1 1+(3154285297/10000000000 : ℝ)*X 1 2+(103372511/250000000 : ℝ)*X 2 0+(1072790599/2000000000 : ℝ)*X 2 1+(3154285297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32004965191977961000167/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7299217/25000000000000 : ℝ)*(base1) + (120657727/20000000000000 : ℝ)*(base19) + (15380653/2500000000000 : ℝ)*(base23) + (19471977/25000000000000 : ℝ)*(upper3) + (37099849/50000000000000 : ℝ)*(upper5) + (724254299517279/100000000000000 : ℝ)*(major0) + (724254299517279/100000000000000 : ℝ)*(major1) + (724254299517279/100000000000000 : ℝ)*(major2) + (254779767806911/25000000000000 : ℝ)*(sp0) + (1019120683712081/100000000000000 : ℝ)*(sp1) + (1019120671774597/100000000000000 : ℝ)*(sp2) + (429386209543671/100000000000000 : ℝ)*(sp3) + (112248497/5000000000000 : ℝ)*(sp4) + (966610081/100000000000000 : ℝ)*(sp7) + (429387205350619/100000000000000 : ℝ)*(f.failure) + (254780321750179/25000000000000 : ℝ)*(f.sum) + (106062066936611/40000000000000000000000000000 : ℝ)*base66 + (68023453656611/80000000000000000000000000000 : ℝ)*base68 + (583632926776611/80000000000000000000000000000 : ℝ)*base70 + (398261090616611/80000000000000000000000000000 : ℝ)*base72 + (27837045863389/40000000000000000000000000000 : ℝ)*base73 + (63757592296611/80000000000000000000000000000 : ℝ)*base76 + (590563378296611/80000000000000000000000000000 : ℝ)*base78 + (606416622536611/80000000000000000000000000000 : ℝ)*base80 + (167437141776611/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5174733/10000000000000000000000 : ℝ)*base89 + (5174733/10000000000000000000000 : ℝ)*base91 + (5174733/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (171405648441145929649383/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1103246503/100000000000000 : ℝ)*(base19) + (631772311/50000000000000 : ℝ)*(base23) + (219007923/50000000000000 : ℝ)*(base39) + (94543747/100000000000000 : ℝ)*(upper3) + (464404269/100000000000000 : ℝ)*(upper5) + (763332678970207/100000000000000 : ℝ)*(major0) + (763332678970207/100000000000000 : ℝ)*(major1) + (763332240954361/100000000000000 : ℝ)*(major2) + (3538600473/100000000000000 : ℝ)*(sp1) + (30589843/1250000000000 : ℝ)*(sp2) + (1074109250672283/100000000000000 : ℝ)*(sp4) + (1074104608825307/100000000000000 : ℝ)*(sp5) + (1074105977956067/100000000000000 : ℝ)*(sp6) + (452555526414239/100000000000000 : ℝ)*(sp7) + (452555526414239/100000000000000 : ℝ)*(f.failure) + (1074109688688129/100000000000000 : ℝ)*(f.sum) + (6259445820961/10000000000000000000000000000 : ℝ)*base65 + (714208944215851/80000000000000000000000000000 : ℝ)*base67 + (72180561328163/80000000000000000000000000000 : ℝ)*base70 + (375778801655851/80000000000000000000000000000 : ℝ)*base71 + (50001714160961/10000000000000000000000000000 : ℝ)*base73 + (15352287488163/80000000000000000000000000000 : ℝ)*base76 + (328175077311837/80000000000000000000000000000 : ℝ)*base77 + (54036080768163/80000000000000000000000000000 : ℝ)*base80 + (44282300471837/40000000000000000000000000000 : ℝ)*base81 + (60187927/10000000000000000000000 : ℝ)*base90 + (60187927/10000000000000000000000 : ℝ)*base92 + (60187927/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1578_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3639/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24657/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1578_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1578_s1_0 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-877304883/5000000000 : ℝ)*x 0 + (5530339051/10000000000 : ℝ)*x 1 + (41023321/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (877304883/5000000000 : ℝ)^4653 ≤ (2147533294139/20000000000000 : ℝ)^3629 := by
    have hnat : (877304883 : ℕ)^4653*20000000000000^3629 ≤ 2147533294139^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877304883 5000000000 2147533294139 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5530339051/10000000000 : ℝ)^4653 ≤ (46791143810293/100000000000000 : ℝ)^3629 := by
    have hnat : (5530339051 : ℕ)^4653*100000000000000^3629 ≤ 46791143810293^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5530339051 10000000000 46791143810293 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41023321/80000000 : ℝ)^4653 ≤ (21235594851073/50000000000000 : ℝ)^3629 := by
    have hnat : (41023321 : ℕ)^4653*50000000000000^3629 ≤ 21235594851073^3629*80000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41023321 80000000 21235594851073 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-877304883/5000000000 : ℝ), (5530339051/10000000000 : ℝ), (41023321/80000000 : ℝ)] ![(2147533294139/20000000000000 : ℝ), (46791143810293/100000000000000 : ℝ), (21235594851073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-877304883/5000000000 : ℝ)|^4653 ≤ (2147533294139/20000000000000 : ℝ)^3629
        have hw : |(-877304883/5000000000 : ℝ)|=(877304883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5530339051/10000000000 : ℝ)|^4653 ≤ (46791143810293/100000000000000 : ℝ)^3629
        have hw : |(5530339051/10000000000 : ℝ)|=(5530339051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41023321/80000000 : ℝ)|^4653 ≤ (21235594851073/50000000000000 : ℝ)^3629
        have hw : |(41023321/80000000 : ℝ)|=(41023321/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s1_1 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687546811/5000000000 : ℝ)*x 0 + (-1964930031/10000000000 : ℝ)*x 1 + (5127914781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687546811/5000000000 : ℝ)^4653 ≤ (22556862265257/50000000000000 : ℝ)^3629 := by
    have hnat : (2687546811 : ℕ)^4653*50000000000000^3629 ≤ 22556862265257^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687546811 5000000000 22556862265257 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1964930031/10000000000 : ℝ)^4653 ≤ (1551886175787/12500000000000 : ℝ)^3629 := by
    have hnat : (1964930031 : ℕ)^4653*12500000000000^3629 ≤ 1551886175787^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964930031 10000000000 1551886175787 12500000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5127914781/10000000000 : ℝ)^4653 ≤ (1698847441963/4000000000000 : ℝ)^3629 := by
    have hnat : (5127914781 : ℕ)^4653*4000000000000^3629 ≤ 1698847441963^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127914781 10000000000 1698847441963 4000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687546811/5000000000 : ℝ), (-1964930031/10000000000 : ℝ), (5127914781/10000000000 : ℝ)] ![(22556862265257/50000000000000 : ℝ), (1551886175787/12500000000000 : ℝ), (1698847441963/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687546811/5000000000 : ℝ)|^4653 ≤ (22556862265257/50000000000000 : ℝ)^3629
        have hw : |(2687546811/5000000000 : ℝ)|=(2687546811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1964930031/10000000000 : ℝ)|^4653 ≤ (1551886175787/12500000000000 : ℝ)^3629
        have hw : |(-1964930031/10000000000 : ℝ)|=(1964930031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5127914781/10000000000 : ℝ)|^4653 ≤ (1698847441963/4000000000000 : ℝ)^3629
        have hw : |(5127914781/10000000000 : ℝ)|=(5127914781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s1_2 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167971669/312500000 : ℝ)*x 0 + (1281978751/2500000000 : ℝ)*x 1 + (-1964930023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167971669/312500000 : ℝ)^4653 ≤ (1804548889103/4000000000000 : ℝ)^3629 := by
    have hnat : (167971669 : ℕ)^4653*4000000000000^3629 ≤ 1804548889103^3629*312500000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167971669 312500000 1804548889103 4000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1281978751/2500000000 : ℝ)^4653 ≤ (42471188417199/100000000000000 : ℝ)^3629 := by
    have hnat : (1281978751 : ℕ)^4653*100000000000000^3629 ≤ 42471188417199^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281978751 2500000000 42471188417199 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1964930023/10000000000 : ℝ)^4653 ≤ (12415089341487/100000000000000 : ℝ)^3629 := by
    have hnat : (1964930023 : ℕ)^4653*100000000000000^3629 ≤ 12415089341487^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964930023 10000000000 12415089341487 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167971669/312500000 : ℝ), (1281978751/2500000000 : ℝ), (-1964930023/10000000000 : ℝ)] ![(1804548889103/4000000000000 : ℝ), (42471188417199/100000000000000 : ℝ), (12415089341487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167971669/312500000 : ℝ)|^4653 ≤ (1804548889103/4000000000000 : ℝ)^3629
        have hw : |(167971669/312500000 : ℝ)|=(167971669/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1281978751/2500000000 : ℝ)|^4653 ≤ (42471188417199/100000000000000 : ℝ)^3629
        have hw : |(1281978751/2500000000 : ℝ)|=(1281978751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1964930023/10000000000 : ℝ)|^4653 ≤ (12415089341487/100000000000000 : ℝ)^3629
        have hw : |(-1964930023/10000000000 : ℝ)|=(1964930023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s1_3 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2112775011/5000000000 : ℝ)*x 0 + (1884802991/5000000000 : ℝ)*x 1 + (590591613/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112775011/5000000000 : ℝ)^4653 ≤ (16568691236437/50000000000000 : ℝ)^3629 := by
    have hnat : (2112775011 : ℕ)^4653*50000000000000^3629 ≤ 16568691236437^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112775011 5000000000 16568691236437 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1884802991/5000000000 : ℝ)^4653 ≤ (14312279234929/50000000000000 : ℝ)^3629 := by
    have hnat : (1884802991 : ℕ)^4653*50000000000000^3629 ≤ 14312279234929^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884802991 5000000000 14312279234929 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (590591613/1250000000 : ℝ)^4653 ≤ (38238059039051/100000000000000 : ℝ)^3629 := by
    have hnat : (590591613 : ℕ)^4653*100000000000000^3629 ≤ 38238059039051^3629*1250000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590591613 1250000000 38238059039051 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2112775011/5000000000 : ℝ), (1884802991/5000000000 : ℝ), (590591613/1250000000 : ℝ)] ![(16568691236437/50000000000000 : ℝ), (14312279234929/50000000000000 : ℝ), (38238059039051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2112775011/5000000000 : ℝ)|^4653 ≤ (16568691236437/50000000000000 : ℝ)^3629
        have hw : |(2112775011/5000000000 : ℝ)|=(2112775011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1884802991/5000000000 : ℝ)|^4653 ≤ (14312279234929/50000000000000 : ℝ)^3629
        have hw : |(1884802991/5000000000 : ℝ)|=(1884802991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(590591613/1250000000 : ℝ)|^4653 ≤ (38238059039051/100000000000000 : ℝ)^3629
        have hw : |(590591613/1250000000 : ℝ)|=(590591613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s1_4 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1754811063/10000000000 : ℝ)*x 0 + (5132021759/10000000000 : ℝ)*x 1 + (5526172539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1754811063/10000000000 : ℝ)^4653 ≤ (10739245971253/100000000000000 : ℝ)^3629 := by
    have hnat : (1754811063 : ℕ)^4653*100000000000000^3629 ≤ 10739245971253^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754811063 10000000000 10739245971253 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5132021759/10000000000 : ℝ)^4653 ≤ (42514804587831/100000000000000 : ℝ)^3629 := by
    have hnat : (5132021759 : ℕ)^4653*100000000000000^3629 ≤ 42514804587831^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132021759 10000000000 42514804587831 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5526172539/10000000000 : ℝ)^4653 ≤ (11686487357071/25000000000000 : ℝ)^3629 := by
    have hnat : (5526172539 : ℕ)^4653*25000000000000^3629 ≤ 11686487357071^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526172539 10000000000 11686487357071 25000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1754811063/10000000000 : ℝ), (5132021759/10000000000 : ℝ), (5526172539/10000000000 : ℝ)] ![(10739245971253/100000000000000 : ℝ), (42514804587831/100000000000000 : ℝ), (11686487357071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1754811063/10000000000 : ℝ)|^4653 ≤ (10739245971253/100000000000000 : ℝ)^3629
        have hw : |(-1754811063/10000000000 : ℝ)|=(1754811063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5132021759/10000000000 : ℝ)|^4653 ≤ (42514804587831/100000000000000 : ℝ)^3629
        have hw : |(5132021759/10000000000 : ℝ)|=(5132021759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5526172539/10000000000 : ℝ)|^4653 ≤ (11686487357071/25000000000000 : ℝ)^3629
        have hw : |(5526172539/10000000000 : ℝ)|=(5526172539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s1_5 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317085063/2500000000 : ℝ)*x 0 + (-313334461/2000000000 : ℝ)*x 1 + (5526173143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317085063/2500000000 : ℝ)^4653 ≤ (43968143407881/100000000000000 : ℝ)^3629 := by
    have hnat : (1317085063 : ℕ)^4653*100000000000000^3629 ≤ 43968143407881^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317085063 2500000000 43968143407881 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (313334461/2000000000 : ℝ)^4653 ≤ (4642950302129/50000000000000 : ℝ)^3629 := by
    have hnat : (313334461 : ℕ)^4653*50000000000000^3629 ≤ 4642950302129^3629*2000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313334461 2000000000 4642950302129 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5526173143/10000000000 : ℝ)^4653 ≤ (5843244497401/12500000000000 : ℝ)^3629 := by
    have hnat : (5526173143 : ℕ)^4653*12500000000000^3629 ≤ 5843244497401^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526173143 10000000000 5843244497401 12500000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317085063/2500000000 : ℝ), (-313334461/2000000000 : ℝ), (5526173143/10000000000 : ℝ)] ![(43968143407881/100000000000000 : ℝ), (4642950302129/50000000000000 : ℝ), (5843244497401/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317085063/2500000000 : ℝ)|^4653 ≤ (43968143407881/100000000000000 : ℝ)^3629
        have hw : |(1317085063/2500000000 : ℝ)|=(1317085063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-313334461/2000000000 : ℝ)|^4653 ≤ (4642950302129/50000000000000 : ℝ)^3629
        have hw : |(-313334461/2000000000 : ℝ)|=(313334461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5526173143/10000000000 : ℝ)|^4653 ≤ (5843244497401/12500000000000 : ℝ)^3629
        have hw : |(5526173143/10000000000 : ℝ)|=(5526173143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s1_6 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5268339529/10000000000 : ℝ)*x 0 + (2763086711/5000000000 : ℝ)*x 1 + (-62666917/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268339529/10000000000 : ℝ)^4653 ≤ (43968135671307/100000000000000 : ℝ)^3629 := by
    have hnat : (5268339529 : ℕ)^4653*100000000000000^3629 ≤ 43968135671307^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268339529 10000000000 43968135671307 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2763086711/5000000000 : ℝ)^4653 ≤ (23372979502607/50000000000000 : ℝ)^3629 := by
    have hnat : (2763086711 : ℕ)^4653*50000000000000^3629 ≤ 23372979502607^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2763086711 5000000000 23372979502607 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62666917/400000000 : ℝ)^4653 ≤ (1160738164503/12500000000000 : ℝ)^3629 := by
    have hnat : (62666917 : ℕ)^4653*12500000000000^3629 ≤ 1160738164503^3629*400000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62666917 400000000 1160738164503 12500000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268339529/10000000000 : ℝ), (2763086711/5000000000 : ℝ), (-62666917/400000000 : ℝ)] ![(43968135671307/100000000000000 : ℝ), (23372979502607/50000000000000 : ℝ), (1160738164503/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268339529/10000000000 : ℝ)|^4653 ≤ (43968135671307/100000000000000 : ℝ)^3629
        have hw : |(5268339529/10000000000 : ℝ)|=(5268339529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2763086711/5000000000 : ℝ)|^4653 ≤ (23372979502607/50000000000000 : ℝ)^3629
        have hw : |(2763086711/5000000000 : ℝ)|=(2763086711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62666917/400000000 : ℝ)|^4653 ≤ (1160738164503/12500000000000 : ℝ)^3629
        have hw : |(-62666917/400000000 : ℝ)|=(62666917/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s1_7 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2113013457/5000000000 : ℝ)*x 0 + (1178746673/2500000000 : ℝ)*x 1 + (37794943/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113013457/5000000000 : ℝ)^4653 ≤ (3314217768683/10000000000000 : ℝ)^3629 := by
    have hnat : (2113013457 : ℕ)^4653*10000000000000^3629 ≤ 3314217768683^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113013457 5000000000 3314217768683 10000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1178746673/2500000000 : ℝ)^4653 ≤ (9534238427861/25000000000000 : ℝ)^3629 := by
    have hnat : (1178746673 : ℕ)^4653*25000000000000^3629 ≤ 9534238427861^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178746673 2500000000 9534238427861 25000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37794943/100000000 : ℝ)^4653 ≤ (28720868594677/100000000000000 : ℝ)^3629 := by
    have hnat : (37794943 : ℕ)^4653*100000000000000^3629 ≤ 28720868594677^3629*100000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37794943 100000000 28720868594677 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2113013457/5000000000 : ℝ), (1178746673/2500000000 : ℝ), (37794943/100000000 : ℝ)] ![(3314217768683/10000000000000 : ℝ), (9534238427861/25000000000000 : ℝ), (28720868594677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2113013457/5000000000 : ℝ)|^4653 ≤ (3314217768683/10000000000000 : ℝ)^3629
        have hw : |(2113013457/5000000000 : ℝ)|=(2113013457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1178746673/2500000000 : ℝ)|^4653 ≤ (9534238427861/25000000000000 : ℝ)^3629
        have hw : |(1178746673/2500000000 : ℝ)|=(1178746673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(37794943/100000000 : ℝ)|^4653 ≤ (28720868594677/100000000000000 : ℝ)^3629
        have hw : |(37794943/100000000 : ℝ)|=(37794943/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1578_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24657/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3639/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4579/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17683/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24657/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3639/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24657/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3639/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24657/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3639/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24657/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3639/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24657/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3639/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24657/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3639/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3639/100000 : ℝ) ^ (4651/1024 : ℝ) ≤ (7276654376493/25000000000000000000 : ℝ) := by
    have hpowers : (3639/100000 : ℝ)^4651 ≤ (7276654376493/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3639 : ℕ)^4651*25000000000000000000^1024 ≤ 7276654376493^1024*100000^4651 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3639 100000 7276654376493 25000000000000000000 4651 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3639/100000 : ℝ)) (X := (7276654376493/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24657/100000 : ℝ) ^ (4651/1024 : ℝ) ≤ (173060238779387791/100000000000000000000 : ℝ) := by
    have hpowers : (24657/100000 : ℝ)^4651 ≤ (173060238779387791/100000000000000000000 : ℝ)^1024 := by
      have hnat : (24657 : ℕ)^4651*100000000000000000000^1024 ≤ 173060238779387791^1024*100000^4651 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24657 100000 173060238779387791 100000000000000000000 4651 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24657/100000 : ℝ)) (X := (173060238779387791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500007276654376493/12500000000000000000 : ℝ) ≤ (200000025633343/200000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (12500007276654376493/12500000000000000000 : ℝ)^1024 ≤ (200000025633343/200000000000000 : ℝ)^4651 := by
      have hnat : (12500007276654376493 : ℕ)^1024*200000000000000^4651 ≤ 200000025633343^4651*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500007276654376493 12500000000000000000 200000025633343 200000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200000025633343/200000000000000 : ℝ)) (X := (12500007276654376493/12500000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100173089345396893763/100000000000000000000 : ℝ) ≤ (312619009346217/312500000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (100173089345396893763/100000000000000000000 : ℝ)^1024 ≤ (312619009346217/312500000000000 : ℝ)^4651 := by
      have hnat : (100173089345396893763 : ℕ)^1024*312500000000000^4651 ≤ 312619009346217^4651*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100173089345396893763 100000000000000000000 312619009346217 312500000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312619009346217/312500000000000 : ℝ)) (X := (100173089345396893763/100000000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50173060238779387791/50000000000000000000 : ℝ) ≤ (5003807658245369/5000000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (50173060238779387791/50000000000000000000 : ℝ)^1024 ≤ (5003807658245369/5000000000000000 : ℝ)^4651 := by
      have hnat : (50173060238779387791 : ℕ)^1024*5000000000000000^4651 ≤ 5003807658245369^4651*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50173060238779387791 50000000000000000000 5003807658245369 5000000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003807658245369/5000000000000000 : ℝ)) (X := (50173060238779387791/50000000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7276654376493/25000000000000000000 : ℝ) ≤ ((4378173322194940041/4378750000000000000 : ℝ)+2*(1903508705897/1050900000000000 : ℝ)*(3639/100000 : ℝ))^(4651/1024 : ℝ) := by
    rw [show (4378173322194940041/4378750000000000000 : ℝ)+2*(1903508705897/1050900000000000 : ℝ)*(3639/100000 : ℝ)=(200000025633343/200000000000000 : ℝ) by norm_num, show 1+2*(7276654376493/25000000000000000000 : ℝ)=(12500007276654376493/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(173060238779387791/100000000000000000000 : ℝ)+(7276654376493/25000000000000000000 : ℝ) ≤ ((4378173322194940041/4378750000000000000 : ℝ)+(1903508705897/1050900000000000 : ℝ)*((24657/100000 : ℝ)+(3639/100000 : ℝ)))^(4651/1024 : ℝ) := by
    rw [show (4378173322194940041/4378750000000000000 : ℝ)+(1903508705897/1050900000000000 : ℝ)*((24657/100000 : ℝ)+(3639/100000 : ℝ))=(312619009346217/312500000000000 : ℝ) by norm_num, show 1+(173060238779387791/100000000000000000000 : ℝ)+(7276654376493/25000000000000000000 : ℝ)=(100173089345396893763/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(173060238779387791/100000000000000000000 : ℝ) ≤ ((4378173322194940041/4378750000000000000 : ℝ)+2*(1903508705897/1050900000000000 : ℝ)*(24657/100000 : ℝ))^(4651/1024 : ℝ) := by
    rw [show (4378173322194940041/4378750000000000000 : ℝ)+2*(1903508705897/1050900000000000 : ℝ)*(24657/100000 : ℝ)=(5003807658245369/5000000000000000 : ℝ) by norm_num, show 1+2*(173060238779387791/100000000000000000000 : ℝ)=(50173060238779387791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4378173322194940041/4378750000000000000 : ℝ)*(X 1 0+X 2 0)+(1903508705897/1050900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (3639/100000 : ℝ)) (hi := (24657/100000 : ℝ)) (c := (4378173322194940041/4378750000000000000 : ℝ)) (alpha := (1903508705897/1050900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4378173322194940041/4378750000000000000 : ℝ)*(X 0 1+X 2 1)+(1903508705897/1050900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (3639/100000 : ℝ)) (hi := (24657/100000 : ℝ)) (c := (4378173322194940041/4378750000000000000 : ℝ)) (alpha := (1903508705897/1050900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4378173322194940041/4378750000000000000 : ℝ)*(X 0 2+X 1 2)+(1903508705897/1050900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (3639/100000 : ℝ)) (hi := (24657/100000 : ℝ)) (c := (4378173322194940041/4378750000000000000 : ℝ)) (alpha := (1903508705897/1050900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-877304883/5000000000 : ℝ)*X 0 0+(5530339051/10000000000 : ℝ)*X 0 1+(41023321/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687546811/5000000000 : ℝ)*X 1 0+(-1964930031/10000000000 : ℝ)*X 1 1+(5127914781/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167971669/312500000 : ℝ)*X 2 0+(1281978751/2500000000 : ℝ)*X 2 1+(-1964930023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2112775011/5000000000 : ℝ)*X 0 0+(1884802991/5000000000 : ℝ)*X 0 1+(590591613/1250000000 : ℝ)*X 0 2+(2112775011/5000000000 : ℝ)*X 1 0+(1884802991/5000000000 : ℝ)*X 1 1+(590591613/1250000000 : ℝ)*X 1 2+(2112775011/5000000000 : ℝ)*X 2 0+(1884802991/5000000000 : ℝ)*X 2 1+(590591613/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1754811063/10000000000 : ℝ)*X 0 0+(5132021759/10000000000 : ℝ)*X 0 1+(5526172539/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1317085063/2500000000 : ℝ)*X 1 0+(-313334461/2000000000 : ℝ)*X 1 1+(5526173143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5268339529/10000000000 : ℝ)*X 2 0+(2763086711/5000000000 : ℝ)*X 2 1+(-62666917/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2113013457/5000000000 : ℝ)*X 0 0+(1178746673/2500000000 : ℝ)*X 0 1+(37794943/100000000 : ℝ)*X 0 2+(2113013457/5000000000 : ℝ)*X 1 0+(1178746673/2500000000 : ℝ)*X 1 1+(37794943/100000000 : ℝ)*X 1 2+(2113013457/5000000000 : ℝ)*X 2 0+(1178746673/2500000000 : ℝ)*X 2 1+(37794943/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (626444119809295282548811737/109468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1733723687/100000000000000 : ℝ)*(base19) + (1580141867/100000000000000 : ℝ)*(base23) + (87581337/50000000000000 : ℝ)*(upper3) + (29373309/100000000000000 : ℝ)*(upper4) + (60797999/50000000000000 : ℝ)*(upper5) + (882991715945931/50000000000000 : ℝ)*(major0) + (882991715945931/50000000000000 : ℝ)*(major1) + (882991715945931/50000000000000 : ℝ)*(major2) + (1213357873561/48828125000 : ℝ)*(sp0) + (621242464049421/25000000000000 : ℝ)*(sp1) + (155310625611219/6250000000000 : ℝ)*(sp2) + (104698797176331/10000000000000 : ℝ)*(sp3) + (14664868443/100000000000000 : ℝ)*(sp4) + (7111346239/100000000000000 : ℝ)*(sp7) + (1046995083109549/100000000000000 : ℝ)*(f.failure) + (2484971589921371/100000000000000 : ℝ)*(f.sum) + (80563475513397/17515000000000000000000000000 : ℝ)*base66 + (941480334333848171/218937500000000000000000000000000 : ℝ)*base67 + (261745440644348171/218937500000000000000000000000000 : ℝ)*base69 + (64587032698839329/218937500000000000000000000000000 : ℝ)*base72 + (12300072343661/8757500000000000000000000000 : ℝ)*base74 + (355769370158035671/218937500000000000000000000000000 : ℝ)*base75 + (2334018176141660671/218937500000000000000000000000000 : ℝ)*base77 + (149821395969464329/218937500000000000000000000000000 : ℝ)*base80 + (7703415986741/8757500000000000000000000000 : ℝ)*base82 + (13124757/10000000000000000000000 : ℝ)*base90 + (13124757/10000000000000000000000 : ℝ)*base92 + (13124757/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1750797881882170580600323767/218937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70171129/5000000000000 : ℝ)*(base19) + (62351957/5000000000000 : ℝ)*(base23) + (55362509/50000000000000 : ℝ)*(upper2) + (61303217/20000000000000 : ℝ)*(upper3) + (125954867/100000000000000 : ℝ)*(upper5) + (1803025521932571/100000000000000 : ℝ)*(major0) + (1803025521932571/100000000000000 : ℝ)*(major1) + (1803025521932571/100000000000000 : ℝ)*(major2) + (2979167789/25000000000000 : ℝ)*(sp1) + (5504867729/50000000000000 : ℝ)*(sp2) + (126854731199199/5000000000000 : ℝ)*(sp4) + (634270325972561/25000000000000 : ℝ)*(sp5) + (1268541183604691/50000000000000 : ℝ)*(sp6) + (1068956153321389/100000000000000 : ℝ)*(sp7) + (1068956153321389/100000000000000 : ℝ)*(f.failure) + (126854731199199/5000000000000 : ℝ)*(f.sum) + (41139937526639/17515000000000000000000000000 : ℝ)*base65 + (367996062916412089/437875000000000000000000000000000 : ℝ)*base68 + (188174773883412089/437875000000000000000000000000000 : ℝ)*base70 + (3374146715686837911/437875000000000000000000000000000 : ℝ)*base71 + (56181881940251/17515000000000000000000000000 : ℝ)*base74 + (718511748176087911/437875000000000000000000000000000 : ℝ)*base75 + (2503802973528587911/437875000000000000000000000000000 : ℝ)*base77 + (665810954002587911/437875000000000000000000000000000 : ℝ)*base79 + (52201911428511/17515000000000000000000000000 : ℝ)*base82 + (29897877/10000000000000000000000 : ℝ)*base90 + (29897877/10000000000000000000000 : ℝ)*base92 + (29897877/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1578_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24657/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3639/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4579/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17683/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1578_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1578_s2_0 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1772499781/10000000000 : ℝ)*x 0 + (2719733161/5000000000 : ℝ)*x 1 + (20828481/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1772499781/10000000000 : ℝ)^4653 ≤ (5439120870911/50000000000000 : ℝ)^3629 := by
    have hnat : (1772499781 : ℕ)^4653*50000000000000^3629 ≤ 5439120870911^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772499781 10000000000 5439120870911 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719733161/5000000000 : ℝ)^4653 ≤ (1431488499929/3125000000000 : ℝ)^3629 := by
    have hnat : (2719733161 : ℕ)^4653*3125000000000^3629 ≤ 1431488499929^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719733161 5000000000 1431488499929 3125000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20828481/40000000 : ℝ)^4653 ≤ (43314126242353/100000000000000 : ℝ)^3629 := by
    have hnat : (20828481 : ℕ)^4653*100000000000000^3629 ≤ 43314126242353^3629*40000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20828481 40000000 43314126242353 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1772499781/10000000000 : ℝ), (2719733161/5000000000 : ℝ), (20828481/40000000 : ℝ)] ![(5439120870911/50000000000000 : ℝ), (1431488499929/3125000000000 : ℝ), (43314126242353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1772499781/10000000000 : ℝ)|^4653 ≤ (5439120870911/50000000000000 : ℝ)^3629
        have hw : |(-1772499781/10000000000 : ℝ)|=(1772499781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719733161/5000000000 : ℝ)|^4653 ≤ (1431488499929/3125000000000 : ℝ)^3629
        have hw : |(2719733161/5000000000 : ℝ)|=(2719733161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20828481/40000000 : ℝ)|^4653 ≤ (43314126242353/100000000000000 : ℝ)^3629
        have hw : |(20828481/40000000 : ℝ)|=(20828481/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s2_1 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337893869/2500000000 : ℝ)*x 0 + (-1891711001/10000000000 : ℝ)*x 1 + (5207120833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337893869/2500000000 : ℝ)^4653 ≤ (44860792773861/100000000000000 : ℝ)^3629 := by
    have hnat : (1337893869 : ℕ)^4653*100000000000000^3629 ≤ 44860792773861^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337893869 2500000000 44860792773861 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1891711001/10000000000 : ℝ)^4653 ≤ (2365014951899/20000000000000 : ℝ)^3629 := by
    have hnat : (1891711001 : ℕ)^4653*20000000000000^3629 ≤ 2365014951899^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891711001 10000000000 2365014951899 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5207120833/10000000000 : ℝ)^4653 ≤ (21657066230147/50000000000000 : ℝ)^3629 := by
    have hnat : (5207120833 : ℕ)^4653*50000000000000^3629 ≤ 21657066230147^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207120833 10000000000 21657066230147 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337893869/2500000000 : ℝ), (-1891711001/10000000000 : ℝ), (5207120833/10000000000 : ℝ)] ![(44860792773861/100000000000000 : ℝ), (2365014951899/20000000000000 : ℝ), (21657066230147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337893869/2500000000 : ℝ)|^4653 ≤ (44860792773861/100000000000000 : ℝ)^3629
        have hw : |(1337893869/2500000000 : ℝ)|=(1337893869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1891711001/10000000000 : ℝ)|^4653 ≤ (2365014951899/20000000000000 : ℝ)^3629
        have hw : |(-1891711001/10000000000 : ℝ)|=(1891711001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5207120833/10000000000 : ℝ)|^4653 ≤ (21657066230147/50000000000000 : ℝ)^3629
        have hw : |(5207120833/10000000000 : ℝ)|=(5207120833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s2_2 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13378939/25000000 : ℝ)*x 0 + (162722519/312500000 : ℝ)*x 1 + (-1891711133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13378939/25000000 : ℝ)^4653 ≤ (358886352853/800000000000 : ℝ)^3629 := by
    have hnat : (13378939 : ℕ)^4653*800000000000^3629 ≤ 358886352853^3629*25000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13378939 25000000 358886352853 800000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162722519/312500000 : ℝ)^4653 ≤ (21657065030287/50000000000000 : ℝ)^3629 := by
    have hnat : (162722519 : ℕ)^4653*50000000000000^3629 ≤ 21657065030287^3629*312500000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162722519 312500000 21657065030287 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1891711133/10000000000 : ℝ)^4653 ≤ (2365015163491/20000000000000 : ℝ)^3629 := by
    have hnat : (1891711133 : ℕ)^4653*20000000000000^3629 ≤ 2365015163491^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891711133 10000000000 2365015163491 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13378939/25000000 : ℝ), (162722519/312500000 : ℝ), (-1891711133/10000000000 : ℝ)] ![(358886352853/800000000000 : ℝ), (21657065030287/50000000000000 : ℝ), (2365015163491/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13378939/25000000 : ℝ)|^4653 ≤ (358886352853/800000000000 : ℝ)^3629
        have hw : |(13378939/25000000 : ℝ)|=(13378939/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162722519/312500000 : ℝ)|^4653 ≤ (21657065030287/50000000000000 : ℝ)^3629
        have hw : |(162722519/312500000 : ℝ)|=(162722519/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1891711133/10000000000 : ℝ)|^4653 ≤ (2365015163491/20000000000000 : ℝ)^3629
        have hw : |(-1891711133/10000000000 : ℝ)|=(1891711133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s2_3 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4238530223/10000000000 : ℝ)*x 0 + (992504107/2500000000 : ℝ)*x 1 + (4521472763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4238530223/10000000000 : ℝ)^4653 ≤ (16633977302551/50000000000000 : ℝ)^3629 := by
    have hnat : (4238530223 : ℕ)^4653*50000000000000^3629 ≤ 16633977302551^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238530223 10000000000 16633977302551 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992504107/2500000000 : ℝ)^4653 ≤ (7647561469267/25000000000000 : ℝ)^3629 := by
    have hnat : (992504107 : ℕ)^4653*25000000000000^3629 ≤ 7647561469267^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992504107 2500000000 7647561469267 25000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4521472763/10000000000 : ℝ)^4653 ≤ (36141799491427/100000000000000 : ℝ)^3629 := by
    have hnat : (4521472763 : ℕ)^4653*100000000000000^3629 ≤ 36141799491427^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521472763 10000000000 36141799491427 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4238530223/10000000000 : ℝ), (992504107/2500000000 : ℝ), (4521472763/10000000000 : ℝ)] ![(16633977302551/50000000000000 : ℝ), (7647561469267/25000000000000 : ℝ), (36141799491427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4238530223/10000000000 : ℝ)|^4653 ≤ (16633977302551/50000000000000 : ℝ)^3629
        have hw : |(4238530223/10000000000 : ℝ)|=(4238530223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(992504107/2500000000 : ℝ)|^4653 ≤ (7647561469267/25000000000000 : ℝ)^3629
        have hw : |(992504107/2500000000 : ℝ)|=(992504107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4521472763/10000000000 : ℝ)|^4653 ≤ (36141799491427/100000000000000 : ℝ)^3629
        have hw : |(4521472763/10000000000 : ℝ)|=(4521472763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s2_4 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1772537673/10000000000 : ℝ)*x 0 + (1302124421/2500000000 : ℝ)*x 1 + (1359519509/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1772537673/10000000000 : ℝ)^4653 ≤ (543926995711/5000000000000 : ℝ)^3629 := by
    have hnat : (1772537673 : ℕ)^4653*5000000000000^3629 ≤ 543926995711^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772537673 10000000000 543926995711 5000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1302124421/2500000000 : ℝ)^4653 ≤ (8665763541039/20000000000000 : ℝ)^3629 := by
    have hnat : (1302124421 : ℕ)^4653*20000000000000^3629 ≤ 8665763541039^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302124421 2500000000 8665763541039 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359519509/2500000000 : ℝ)^4653 ≤ (45792642366851/100000000000000 : ℝ)^3629 := by
    have hnat : (1359519509 : ℕ)^4653*100000000000000^3629 ≤ 45792642366851^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359519509 2500000000 45792642366851 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1772537673/10000000000 : ℝ), (1302124421/2500000000 : ℝ), (1359519509/2500000000 : ℝ)] ![(543926995711/5000000000000 : ℝ), (8665763541039/20000000000000 : ℝ), (45792642366851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1772537673/10000000000 : ℝ)|^4653 ≤ (543926995711/5000000000000 : ℝ)^3629
        have hw : |(-1772537673/10000000000 : ℝ)|=(1772537673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1302124421/2500000000 : ℝ)|^4653 ≤ (8665763541039/20000000000000 : ℝ)^3629
        have hw : |(1302124421/2500000000 : ℝ)|=(1302124421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359519509/2500000000 : ℝ)|^4653 ≤ (45792642366851/100000000000000 : ℝ)^3629
        have hw : |(1359519509/2500000000 : ℝ)|=(1359519509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s2_5 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290040591/10000000000 : ℝ)*x 0 + (-332150849/2000000000 : ℝ)*x 1 + (1359519763/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290040591/10000000000 : ℝ)^4653 ≤ (44200486077967/100000000000000 : ℝ)^3629 := by
    have hnat : (5290040591 : ℕ)^4653*100000000000000^3629 ≤ 44200486077967^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290040591 10000000000 44200486077967 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (332150849/2000000000 : ℝ)^4653 ≤ (10006860567403/100000000000000 : ℝ)^3629 := by
    have hnat : (332150849 : ℕ)^4653*100000000000000^3629 ≤ 10006860567403^3629*2000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332150849 2000000000 10006860567403 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359519763/2500000000 : ℝ)^4653 ≤ (45792653336433/100000000000000 : ℝ)^3629 := by
    have hnat : (1359519763 : ℕ)^4653*100000000000000^3629 ≤ 45792653336433^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359519763 2500000000 45792653336433 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290040591/10000000000 : ℝ), (-332150849/2000000000 : ℝ), (1359519763/2500000000 : ℝ)] ![(44200486077967/100000000000000 : ℝ), (10006860567403/100000000000000 : ℝ), (45792653336433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290040591/10000000000 : ℝ)|^4653 ≤ (44200486077967/100000000000000 : ℝ)^3629
        have hw : |(5290040591/10000000000 : ℝ)|=(5290040591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-332150849/2000000000 : ℝ)|^4653 ≤ (10006860567403/100000000000000 : ℝ)^3629
        have hw : |(-332150849/2000000000 : ℝ)|=(332150849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359519763/2500000000 : ℝ)|^4653 ≤ (45792653336433/100000000000000 : ℝ)^3629
        have hw : |(1359519763/2500000000 : ℝ)|=(1359519763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s2_6 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058008213/2000000000 : ℝ)*x 0 + (5438080201/10000000000 : ℝ)*x 1 + (-1660751983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058008213/2000000000 : ℝ)^4653 ≤ (11050122788991/25000000000000 : ℝ)^3629 := by
    have hnat : (1058008213 : ℕ)^4653*25000000000000^3629 ≤ 11050122788991^3629*2000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058008213 2000000000 11050122788991 25000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438080201/10000000000 : ℝ)^4653 ≤ (22896332870997/50000000000000 : ℝ)^3629 := by
    have hnat : (5438080201 : ℕ)^4653*50000000000000^3629 ≤ 22896332870997^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438080201 10000000000 22896332870997 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1660751983/10000000000 : ℝ)^4653 ≤ (2501710772961/25000000000000 : ℝ)^3629 := by
    have hnat : (1660751983 : ℕ)^4653*25000000000000^3629 ≤ 2501710772961^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660751983 10000000000 2501710772961 25000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058008213/2000000000 : ℝ), (5438080201/10000000000 : ℝ), (-1660751983/10000000000 : ℝ)] ![(11050122788991/25000000000000 : ℝ), (22896332870997/50000000000000 : ℝ), (2501710772961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058008213/2000000000 : ℝ)|^4653 ≤ (11050122788991/25000000000000 : ℝ)^3629
        have hw : |(1058008213/2000000000 : ℝ)|=(1058008213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438080201/10000000000 : ℝ)|^4653 ≤ (22896332870997/50000000000000 : ℝ)^3629
        have hw : |(5438080201/10000000000 : ℝ)|=(5438080201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1660751983/10000000000 : ℝ)|^4653 ≤ (2501710772961/25000000000000 : ℝ)^3629
        have hw : |(-1660751983/10000000000 : ℝ)|=(1660751983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s2_7 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (847724641/2000000000 : ℝ)*x 0 + (4518205243/10000000000 : ℝ)*x 1 + (3973310653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847724641/2000000000 : ℝ)^4653 ≤ (8317222587317/25000000000000 : ℝ)^3629 := by
    have hnat : (847724641 : ℕ)^4653*25000000000000^3629 ≤ 8317222587317^3629*2000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847724641 2000000000 8317222587317 25000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518205243/10000000000 : ℝ)^4653 ≤ (7221662904469/20000000000000 : ℝ)^3629 := by
    have hnat : (4518205243 : ℕ)^4653*20000000000000^3629 ≤ 7221662904469^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518205243 10000000000 7221662904469 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3973310653/10000000000 : ℝ)^4653 ≤ (15311397557933/50000000000000 : ℝ)^3629 := by
    have hnat : (3973310653 : ℕ)^4653*50000000000000^3629 ≤ 15311397557933^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3973310653 10000000000 15311397557933 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(847724641/2000000000 : ℝ), (4518205243/10000000000 : ℝ), (3973310653/10000000000 : ℝ)] ![(8317222587317/25000000000000 : ℝ), (7221662904469/20000000000000 : ℝ), (15311397557933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(847724641/2000000000 : ℝ)|^4653 ≤ (8317222587317/25000000000000 : ℝ)^3629
        have hw : |(847724641/2000000000 : ℝ)|=(847724641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518205243/10000000000 : ℝ)|^4653 ≤ (7221662904469/20000000000000 : ℝ)^3629
        have hw : |(4518205243/10000000000 : ℝ)|=(4518205243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3973310653/10000000000 : ℝ)|^4653 ≤ (15311397557933/50000000000000 : ℝ)^3629
        have hw : |(3973310653/10000000000 : ℝ)|=(3973310653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1578_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (679/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15791/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17683/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4579/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17683/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4579/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17683/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4579/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17683/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4579/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17683/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4579/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17683/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4579/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4579/50000 : ℝ) ^ (4651/1024 : ℝ) ≤ (1925336367000887/100000000000000000000 : ℝ) := by
    have hpowers : (4579/50000 : ℝ)^4651 ≤ (1925336367000887/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4579 : ℕ)^4651*100000000000000000000^1024 ≤ 1925336367000887^1024*50000^4651 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4579 50000 1925336367000887 100000000000000000000 4651 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4579/50000 : ℝ)) (X := (1925336367000887/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17683/100000 : ℝ) ^ (4651/1024 : ℝ) ≤ (38230060862296547/100000000000000000000 : ℝ) := by
    have hpowers : (17683/100000 : ℝ)^4651 ≤ (38230060862296547/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17683 : ℕ)^4651*100000000000000000000^1024 ≤ 38230060862296547^1024*100000^4651 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17683 100000 38230060862296547 100000000000000000000 4651 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17683/100000 : ℝ)) (X := (38230060862296547/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001925336367000887/50000000000000000000 : ℝ) ≤ (10000084778105309/10000000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (50001925336367000887/50000000000000000000 : ℝ)^1024 ≤ (10000084778105309/10000000000000000 : ℝ)^4651 := by
      have hnat : (50001925336367000887 : ℕ)^1024*10000000000000000^4651 ≤ 10000084778105309^4651*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001925336367000887 50000000000000000000 10000084778105309 10000000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084778105309/10000000000000000 : ℝ)) (X := (50001925336367000887/50000000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020077698614648717/50000000000000000000 : ℝ) ≤ (5000441976888591/5000000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (50020077698614648717/50000000000000000000 : ℝ)^1024 ≤ (5000441976888591/5000000000000000 : ℝ)^4651 := by
      have hnat : (50020077698614648717 : ℕ)^1024*5000000000000000^4651 ≤ 5000441976888591^4651*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020077698614648717 50000000000000000000 5000441976888591 5000000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000441976888591/5000000000000000 : ℝ)) (X := (50020077698614648717/50000000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038230060862296547/50000000000000000000 : ℝ) ≤ (2000336625889811/2000000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (50038230060862296547/50000000000000000000 : ℝ)^1024 ≤ (2000336625889811/2000000000000000 : ℝ)^4651 := by
      have hnat : (50038230060862296547 : ℕ)^1024*2000000000000000^4651 ≤ 2000336625889811^4651*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038230060862296547 50000000000000000000 2000336625889811 2000000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000336625889811/2000000000000000 : ℝ)) (X := (50038230060862296547/50000000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1925336367000887/100000000000000000000 : ℝ) ≤ ((2749551130056184947/2750000000000000000 : ℝ)+2*(25779860383/27500000000000 : ℝ)*(4579/50000 : ℝ))^(4651/1024 : ℝ) := by
    rw [show (2749551130056184947/2750000000000000000 : ℝ)+2*(25779860383/27500000000000 : ℝ)*(4579/50000 : ℝ)=(10000084778105309/10000000000000000 : ℝ) by norm_num, show 1+2*(1925336367000887/100000000000000000000 : ℝ)=(50001925336367000887/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38230060862296547/100000000000000000000 : ℝ)+(1925336367000887/100000000000000000000 : ℝ) ≤ ((2749551130056184947/2750000000000000000 : ℝ)+(25779860383/27500000000000 : ℝ)*((17683/100000 : ℝ)+(4579/50000 : ℝ)))^(4651/1024 : ℝ) := by
    rw [show (2749551130056184947/2750000000000000000 : ℝ)+(25779860383/27500000000000 : ℝ)*((17683/100000 : ℝ)+(4579/50000 : ℝ))=(5000441976888591/5000000000000000 : ℝ) by norm_num, show 1+(38230060862296547/100000000000000000000 : ℝ)+(1925336367000887/100000000000000000000 : ℝ)=(50020077698614648717/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38230060862296547/100000000000000000000 : ℝ) ≤ ((2749551130056184947/2750000000000000000 : ℝ)+2*(25779860383/27500000000000 : ℝ)*(17683/100000 : ℝ))^(4651/1024 : ℝ) := by
    rw [show (2749551130056184947/2750000000000000000 : ℝ)+2*(25779860383/27500000000000 : ℝ)*(17683/100000 : ℝ)=(2000336625889811/2000000000000000 : ℝ) by norm_num, show 1+2*(38230060862296547/100000000000000000000 : ℝ)=(50038230060862296547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2749551130056184947/2750000000000000000 : ℝ)*(X 1 0+X 2 0)+(25779860383/27500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (4579/50000 : ℝ)) (hi := (17683/100000 : ℝ)) (c := (2749551130056184947/2750000000000000000 : ℝ)) (alpha := (25779860383/27500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2749551130056184947/2750000000000000000 : ℝ)*(X 0 1+X 2 1)+(25779860383/27500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (4579/50000 : ℝ)) (hi := (17683/100000 : ℝ)) (c := (2749551130056184947/2750000000000000000 : ℝ)) (alpha := (25779860383/27500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2749551130056184947/2750000000000000000 : ℝ)*(X 0 2+X 1 2)+(25779860383/27500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (4579/50000 : ℝ)) (hi := (17683/100000 : ℝ)) (c := (2749551130056184947/2750000000000000000 : ℝ)) (alpha := (25779860383/27500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1772499781/10000000000 : ℝ)*X 0 0+(2719733161/5000000000 : ℝ)*X 0 1+(20828481/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337893869/2500000000 : ℝ)*X 1 0+(-1891711001/10000000000 : ℝ)*X 1 1+(5207120833/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((13378939/25000000 : ℝ)*X 2 0+(162722519/312500000 : ℝ)*X 2 1+(-1891711133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4238530223/10000000000 : ℝ)*X 0 0+(992504107/2500000000 : ℝ)*X 0 1+(4521472763/10000000000 : ℝ)*X 0 2+(4238530223/10000000000 : ℝ)*X 1 0+(992504107/2500000000 : ℝ)*X 1 1+(4521472763/10000000000 : ℝ)*X 1 2+(4238530223/10000000000 : ℝ)*X 2 0+(992504107/2500000000 : ℝ)*X 2 1+(4521472763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1772537673/10000000000 : ℝ)*X 0 0+(1302124421/2500000000 : ℝ)*X 0 1+(1359519509/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290040591/10000000000 : ℝ)*X 1 0+(-332150849/2000000000 : ℝ)*X 1 1+(1359519763/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058008213/2000000000 : ℝ)*X 2 0+(5438080201/10000000000 : ℝ)*X 2 1+(-1660751983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((847724641/2000000000 : ℝ)*X 0 0+(4518205243/10000000000 : ℝ)*X 0 1+(3973310653/10000000000 : ℝ)*X 0 2+(847724641/2000000000 : ℝ)*X 1 0+(4518205243/10000000000 : ℝ)*X 1 1+(3973310653/10000000000 : ℝ)*X 1 2+(847724641/2000000000 : ℝ)*X 2 0+(4518205243/10000000000 : ℝ)*X 2 1+(3973310653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24268805668413968836622973/4296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (863746471/100000000000000 : ℝ)*(base19) + (431565889/50000000000000 : ℝ)*(base23) + (6650147/5000000000000 : ℝ)*(upper2) + (87811237/50000000000000 : ℝ)*(upper3) + (186701117/100000000000000 : ℝ)*(upper4) + (191167673967953/6250000000000 : ℝ)*(major0) + (191167673967953/6250000000000 : ℝ)*(major1) + (3058682783487249/100000000000000 : ℝ)*(major2) + (860789803691643/20000000000000 : ℝ)*(sp0) + (2151984669816151/50000000000000 : ℝ)*(sp1) + (860793868049399/20000000000000 : ℝ)*(sp2) + (1813386561087359/100000000000000 : ℝ)*(sp3) + (21184920557/100000000000000 : ℝ)*(sp4) + (430712063/5000000000000 : ℝ)*(sp7) + (1813395175328619/100000000000000 : ℝ)*(f.failure) + (1075992550844693/25000000000000 : ℝ)*(f.sum) + (267041222309/250000000000000000000000000 : ℝ)*base66 + (10606647895507069/1562500000000000000000000000000 : ℝ)*base68 + (72968453721240073/25000000000000000000000000000000 : ℝ)*base69 + (5760913612694569/1562500000000000000000000000000 : ℝ)*base72 + (219381040441/250000000000000000000000000 : ℝ)*base73 + (221331740378759927/25000000000000000000000000000000 : ℝ)*base76 + (135283765629534009/17187500000000000000000000000000 : ℝ)*base78 + (78323040293596509/17187500000000000000000000000000 : ℝ)*base80 + (4269997074117/687500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (119820733/10000000000000000000000 : ℝ)*base89 + (119820733/10000000000000000000000 : ℝ)*base91 + (19820733/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1528466287480957940547945159/137500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33830879/10000000000000 : ℝ)*(base15) + (54418881/20000000000000 : ℝ)*(lower2) + (100251443/100000000000000 : ℝ)*(upper3) + (17567/400000000000 : ℝ)*(upper4) + (619100007913683/20000000000000 : ℝ)*(major0) + (619100007913683/20000000000000 : ℝ)*(major1) + (96734376236513/3125000000000 : ℝ)*(major2) + (6854940349/100000000000000 : ℝ)*(sp1) + (22064536697/50000000000000 : ℝ)*(sp2) + (250205183/20000000000000 : ℝ)*(sp3) + (174231070396851/4000000000000 : ℝ)*(sp4) + (544471195834017/12500000000000 : ℝ)*(sp5) + (2177866315423941/50000000000000 : ℝ)*(sp6) + (1835221697652351/100000000000000 : ℝ)*(sp7) + (917611474339133/50000000000000 : ℝ)*(f.failure) + (174231070396851/4000000000000 : ℝ)*(f.sum) + (3694870522523/2750000000000000000000000000 : ℝ)*base65 + (367137176588510199/55000000000000000000000000000000 : ℝ)*base68 + (4467506724415367/1074218750000000000000000000000 : ℝ)*base69 + (785115436626489801/55000000000000000000000000000000 : ℝ)*base71 + (9209422854727/2750000000000000000000000000 : ℝ)*base74 + (19084882843364593/4296875000000000000000000000000 : ℝ)*base75 + (101335058231170199/55000000000000000000000000000000 : ℝ)*base78 + (693751114166170199/55000000000000000000000000000000 : ℝ)*base80 + (2185137012089/275000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (76096731/5000000000000000000000 : ℝ)*base89 + (76096731/5000000000000000000000 : ℝ)*base91 + (26096731/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1578_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (679/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15791/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1578_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1578_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (679/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15791/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1578_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1578_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1578_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (679/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15791/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1578_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
