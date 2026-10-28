-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1203_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:03:57.096784+00:00
-- url     : https://prove2.me/submissions/a34012e5-0245-488c-89c2-a01c1a79784b

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
theorem support_rectangle_w1203_s0_0 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-468163423/2500000000 : ℝ)*x 0 + (6040338347/10000000000 : ℝ)*x 1 + (957627711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (468163423/2500000000 : ℝ)^2099 ≤ (10907789696711/100000000000000 : ℝ)^1587 := by
    have hnat : (468163423 : ℕ)^2099*100000000000000^1587 ≤ 10907789696711^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468163423 2500000000 10907789696711 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6040338347/10000000000 : ℝ)^2099 ≤ (51336584095227/100000000000000 : ℝ)^1587 := by
    have hnat : (6040338347 : ℕ)^2099*100000000000000^1587 ≤ 51336584095227^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6040338347 10000000000 51336584095227 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957627711/2000000000 : ℝ)^2099 ≤ (9438906550001/25000000000000 : ℝ)^1587 := by
    have hnat : (957627711 : ℕ)^2099*25000000000000^1587 ≤ 9438906550001^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957627711 2000000000 9438906550001 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-468163423/2500000000 : ℝ), (6040338347/10000000000 : ℝ), (957627711/2000000000 : ℝ)] ![(10907789696711/100000000000000 : ℝ), (51336584095227/100000000000000 : ℝ), (9438906550001/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-468163423/2500000000 : ℝ)|^2099 ≤ (10907789696711/100000000000000 : ℝ)^1587
        have hw : |(-468163423/2500000000 : ℝ)|=(468163423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6040338347/10000000000 : ℝ)|^2099 ≤ (51336584095227/100000000000000 : ℝ)^1587
        have hw : |(6040338347/10000000000 : ℝ)|=(6040338347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(957627711/2000000000 : ℝ)|^2099 ≤ (9438906550001/25000000000000 : ℝ)^1587
        have hw : |(957627711/2000000000 : ℝ)|=(957627711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s0_1 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1378339117/2500000000 : ℝ)*x 0 + (-647393487/2500000000 : ℝ)*x 1 + (478813853/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378339117/2500000000 : ℝ)^2099 ≤ (45497904063147/100000000000000 : ℝ)^1587 := by
    have hnat : (1378339117 : ℕ)^2099*100000000000000^1587 ≤ 45497904063147^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378339117 2500000000 45497904063147 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647393487/2500000000 : ℝ)^2099 ≤ (1046654373889/6250000000000 : ℝ)^1587 := by
    have hnat : (647393487 : ℕ)^2099*6250000000000^1587 ≤ 1046654373889^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647393487 2500000000 1046654373889 6250000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478813853/1000000000 : ℝ)^2099 ≤ (18877812969637/50000000000000 : ℝ)^1587 := by
    have hnat : (478813853 : ℕ)^2099*50000000000000^1587 ≤ 18877812969637^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478813853 1000000000 18877812969637 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378339117/2500000000 : ℝ), (-647393487/2500000000 : ℝ), (478813853/1000000000 : ℝ)] ![(45497904063147/100000000000000 : ℝ), (1046654373889/6250000000000 : ℝ), (18877812969637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378339117/2500000000 : ℝ)|^2099 ≤ (45497904063147/100000000000000 : ℝ)^1587
        have hw : |(1378339117/2500000000 : ℝ)|=(1378339117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-647393487/2500000000 : ℝ)|^2099 ≤ (1046654373889/6250000000000 : ℝ)^1587
        have hw : |(-647393487/2500000000 : ℝ)|=(647393487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(478813853/1000000000 : ℝ)|^2099 ≤ (18877812969637/50000000000000 : ℝ)^1587
        have hw : |(478813853/1000000000 : ℝ)|=(478813853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s0_2 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1378339213/2500000000 : ℝ)*x 0 + (4788138157/10000000000 : ℝ)*x 1 + (-2589573913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378339213/2500000000 : ℝ)^2099 ≤ (22748954127191/50000000000000 : ℝ)^1587 := by
    have hnat : (1378339213 : ℕ)^2099*50000000000000^1587 ≤ 22748954127191^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378339213 2500000000 22748954127191 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4788138157/10000000000 : ℝ)^2099 ≤ (9438905512297/25000000000000 : ℝ)^1587 := by
    have hnat : (4788138157 : ℕ)^2099*25000000000000^1587 ≤ 9438905512297^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4788138157 10000000000 9438905512297 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589573913/10000000000 : ℝ)^2099 ≤ (16746469682861/100000000000000 : ℝ)^1587 := by
    have hnat : (2589573913 : ℕ)^2099*100000000000000^1587 ≤ 16746469682861^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589573913 10000000000 16746469682861 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378339213/2500000000 : ℝ), (4788138157/10000000000 : ℝ), (-2589573913/10000000000 : ℝ)] ![(22748954127191/50000000000000 : ℝ), (9438905512297/25000000000000 : ℝ), (16746469682861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378339213/2500000000 : ℝ)|^2099 ≤ (22748954127191/50000000000000 : ℝ)^1587
        have hw : |(1378339213/2500000000 : ℝ)|=(1378339213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4788138157/10000000000 : ℝ)|^2099 ≤ (9438905512297/25000000000000 : ℝ)^1587
        have hw : |(4788138157/10000000000 : ℝ)|=(4788138157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2589573913/10000000000 : ℝ)|^2099 ≤ (16746469682861/100000000000000 : ℝ)^1587
        have hw : |(-2589573913/10000000000 : ℝ)|=(2589573913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s0_3 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (262256371/625000000 : ℝ)*x 0 + (1559209861/5000000000 : ℝ)*x 1 + (1127896217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262256371/625000000 : ℝ)^2099 ≤ (31707947219483/100000000000000 : ℝ)^1587 := by
    have hnat : (262256371 : ℕ)^2099*100000000000000^1587 ≤ 31707947219483^1587*625000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262256371 625000000 31707947219483 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1559209861/5000000000 : ℝ)^2099 ≤ (21412485504983/100000000000000 : ℝ)^1587 := by
    have hnat : (1559209861 : ℕ)^2099*100000000000000^1587 ≤ 21412485504983^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559209861 5000000000 21412485504983 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127896217/2000000000 : ℝ)^2099 ≤ (9375913454201/20000000000000 : ℝ)^1587 := by
    have hnat : (1127896217 : ℕ)^2099*20000000000000^1587 ≤ 9375913454201^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127896217 2000000000 9375913454201 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262256371/625000000 : ℝ), (1559209861/5000000000 : ℝ), (1127896217/2000000000 : ℝ)] ![(31707947219483/100000000000000 : ℝ), (21412485504983/100000000000000 : ℝ), (9375913454201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262256371/625000000 : ℝ)|^2099 ≤ (31707947219483/100000000000000 : ℝ)^1587
        have hw : |(262256371/625000000 : ℝ)|=(262256371/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1559209861/5000000000 : ℝ)|^2099 ≤ (21412485504983/100000000000000 : ℝ)^1587
        have hw : |(1559209861/5000000000 : ℝ)|=(1559209861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127896217/2000000000 : ℝ)|^2099 ≤ (9375913454201/20000000000000 : ℝ)^1587
        have hw : |(1127896217/2000000000 : ℝ)|=(1127896217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s0_4 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-234702819/1250000000 : ℝ)*x 0 + (1205102363/2500000000 : ℝ)*x 1 + (3003464269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234702819/1250000000 : ℝ)^2099 ≤ (85516297177/781250000000 : ℝ)^1587 := by
    have hnat : (234702819 : ℕ)^2099*781250000000^1587 ≤ 85516297177^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234702819 1250000000 85516297177 781250000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1205102363/2500000000 : ℝ)^2099 ≤ (304740406317/800000000000 : ℝ)^1587 := by
    have hnat : (1205102363 : ℕ)^2099*800000000000^1587 ≤ 304740406317^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205102363 2500000000 304740406317 800000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3003464269/5000000000 : ℝ)^2099 ≤ (50961363163039/100000000000000 : ℝ)^1587 := by
    have hnat : (3003464269 : ℕ)^2099*100000000000000^1587 ≤ 50961363163039^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3003464269 5000000000 50961363163039 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-234702819/1250000000 : ℝ), (1205102363/2500000000 : ℝ), (3003464269/5000000000 : ℝ)] ![(85516297177/781250000000 : ℝ), (304740406317/800000000000 : ℝ), (50961363163039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-234702819/1250000000 : ℝ)|^2099 ≤ (85516297177/781250000000 : ℝ)^1587
        have hw : |(-234702819/1250000000 : ℝ)|=(234702819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1205102363/2500000000 : ℝ)|^2099 ≤ (304740406317/800000000000 : ℝ)^1587
        have hw : |(1205102363/2500000000 : ℝ)|=(1205102363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3003464269/5000000000 : ℝ)|^2099 ≤ (50961363163039/100000000000000 : ℝ)^1587
        have hw : |(3003464269/5000000000 : ℝ)|=(3003464269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s0_5 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5172821483/10000000000 : ℝ)*x 0 + (-1370782183/10000000000 : ℝ)*x 1 + (1501732521/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5172821483/10000000000 : ℝ)^2099 ≤ (4181863784213/10000000000000 : ℝ)^1587 := by
    have hnat : (5172821483 : ℕ)^2099*10000000000000^1587 ≤ 4181863784213^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172821483 10000000000 4181863784213 10000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1370782183/10000000000 : ℝ)^2099 ≤ (3609990813199/50000000000000 : ℝ)^1587 := by
    have hnat : (1370782183 : ℕ)^2099*50000000000000^1587 ≤ 3609990813199^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370782183 10000000000 3609990813199 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1501732521/2500000000 : ℝ)^2099 ≤ (50961380510407/100000000000000 : ℝ)^1587 := by
    have hnat : (1501732521 : ℕ)^2099*100000000000000^1587 ≤ 50961380510407^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501732521 2500000000 50961380510407 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5172821483/10000000000 : ℝ), (-1370782183/10000000000 : ℝ), (1501732521/2500000000 : ℝ)] ![(4181863784213/10000000000000 : ℝ), (3609990813199/50000000000000 : ℝ), (50961380510407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5172821483/10000000000 : ℝ)|^2099 ≤ (4181863784213/10000000000000 : ℝ)^1587
        have hw : |(5172821483/10000000000 : ℝ)|=(5172821483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1370782183/10000000000 : ℝ)|^2099 ≤ (3609990813199/50000000000000 : ℝ)^1587
        have hw : |(-1370782183/10000000000 : ℝ)|=(1370782183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1501732521/2500000000 : ℝ)|^2099 ≤ (50961380510407/100000000000000 : ℝ)^1587
        have hw : |(1501732521/2500000000 : ℝ)|=(1501732521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s0_6 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1034564447/2000000000 : ℝ)*x 0 + (3003464523/5000000000 : ℝ)*x 1 + (-1370782703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034564447/2000000000 : ℝ)^2099 ≤ (20909322941433/50000000000000 : ℝ)^1587 := by
    have hnat : (1034564447 : ℕ)^2099*50000000000000^1587 ≤ 20909322941433^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034564447 2000000000 20909322941433 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3003464523/5000000000 : ℝ)^2099 ≤ (6370171107901/12500000000000 : ℝ)^1587 := by
    have hnat : (3003464523 : ℕ)^2099*12500000000000^1587 ≤ 6370171107901^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3003464523 5000000000 6370171107901 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370782703/10000000000 : ℝ)^2099 ≤ (7219985248883/100000000000000 : ℝ)^1587 := by
    have hnat : (1370782703 : ℕ)^2099*100000000000000^1587 ≤ 7219985248883^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370782703 10000000000 7219985248883 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034564447/2000000000 : ℝ), (3003464523/5000000000 : ℝ), (-1370782703/10000000000 : ℝ)] ![(20909322941433/50000000000000 : ℝ), (6370171107901/12500000000000 : ℝ), (7219985248883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034564447/2000000000 : ℝ)|^2099 ≤ (20909322941433/50000000000000 : ℝ)^1587
        have hw : |(1034564447/2000000000 : ℝ)|=(1034564447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3003464523/5000000000 : ℝ)|^2099 ≤ (6370171107901/12500000000000 : ℝ)^1587
        have hw : |(3003464523/5000000000 : ℝ)|=(3003464523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1370782703/10000000000 : ℝ)|^2099 ≤ (7219985248883/100000000000000 : ℝ)^1587
        have hw : |(-1370782703/10000000000 : ℝ)|=(1370782703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s0_7 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4206104877/10000000000 : ℝ)*x 0 + (222980521/400000000 : ℝ)*x 1 + (1592840103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206104877/10000000000 : ℝ)^2099 ≤ (31807959239387/100000000000000 : ℝ)^1587 := by
    have hnat : (4206104877 : ℕ)^2099*100000000000000^1587 ≤ 31807959239387^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206104877 10000000000 31807959239387 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222980521/400000000 : ℝ)^2099 ≤ (46166599445383/100000000000000 : ℝ)^1587 := by
    have hnat : (222980521 : ℕ)^2099*100000000000000^1587 ≤ 46166599445383^1587*400000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222980521 400000000 46166599445383 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1592840103/5000000000 : ℝ)^2099 ≤ (2202544129541/10000000000000 : ℝ)^1587 := by
    have hnat : (1592840103 : ℕ)^2099*10000000000000^1587 ≤ 2202544129541^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592840103 5000000000 2202544129541 10000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206104877/10000000000 : ℝ), (222980521/400000000 : ℝ), (1592840103/5000000000 : ℝ)] ![(31807959239387/100000000000000 : ℝ), (46166599445383/100000000000000 : ℝ), (2202544129541/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206104877/10000000000 : ℝ)|^2099 ≤ (31807959239387/100000000000000 : ℝ)^1587
        have hw : |(4206104877/10000000000 : ℝ)|=(4206104877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(222980521/400000000 : ℝ)|^2099 ≤ (46166599445383/100000000000000 : ℝ)^1587
        have hw : |(222980521/400000000 : ℝ)|=(222980521/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1592840103/5000000000 : ℝ)|^2099 ≤ (2202544129541/10000000000000 : ℝ)^1587
        have hw : |(1592840103/5000000000 : ℝ)|=(1592840103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1203_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (331/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27583/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8395/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8395 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8395*1^2048 ≤ 0^2048*1^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8395/2048 : ℝ) ≤ (2337737354260076777/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8395 ≤ (2337737354260076777/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8395*100000000000000000000^2048 ≤ 2337737354260076777^2048*5^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2337737354260076777 100000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2337737354260076777/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8395 := by
      have hnat : (1 : ℕ)^2048*1^8395 ≤ 1^8395*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102337737354260076777/100000000000000000000 : ℝ) ≤ (2011306602196069/2000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (102337737354260076777/100000000000000000000 : ℝ)^2048 ≤ (2011306602196069/2000000000000000 : ℝ)^8395 := by
      have hnat : (102337737354260076777 : ℕ)^2048*2000000000000000^8395 ≤ 2011306602196069^8395*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102337737354260076777 100000000000000000000 2011306602196069 2000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011306602196069/2000000000000000 : ℝ)) (X := (102337737354260076777/100000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52337737354260076777/50000000000000000000 : ℝ) ≤ (1011306602196069/1000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (52337737354260076777/50000000000000000000 : ℝ)^2048 ≤ (1011306602196069/1000000000000000 : ℝ)^8395 := by
      have hnat : (52337737354260076777 : ℕ)^2048*1000000000000000^8395 ≤ 1011306602196069^8395*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52337737354260076777 50000000000000000000 1011306602196069 1000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011306602196069/1000000000000000 : ℝ)) (X := (52337737354260076777/50000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11306602196069/800000000000000 : ℝ)*(0 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11306602196069/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2337737354260076777/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11306602196069/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8395/2048 : ℝ) := by
    rw [show (1 : ℝ)+(11306602196069/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2011306602196069/2000000000000000 : ℝ) by norm_num, show 1+(2337737354260076777/100000000000000000000 : ℝ)+(0 : ℝ)=(102337737354260076777/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2337737354260076777/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11306602196069/800000000000000 : ℝ)*(2/5 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11306602196069/800000000000000 : ℝ)*(2/5 : ℝ)=(1011306602196069/1000000000000000 : ℝ) by norm_num, show 1+2*(2337737354260076777/100000000000000000000 : ℝ)=(52337737354260076777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11306602196069/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11306602196069/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11306602196069/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11306602196069/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11306602196069/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11306602196069/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-468163423/2500000000 : ℝ)*X 0 0+(6040338347/10000000000 : ℝ)*X 0 1+(957627711/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1378339117/2500000000 : ℝ)*X 1 0+(-647393487/2500000000 : ℝ)*X 1 1+(478813853/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1378339213/2500000000 : ℝ)*X 2 0+(4788138157/10000000000 : ℝ)*X 2 1+(-2589573913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((262256371/625000000 : ℝ)*X 0 0+(1559209861/5000000000 : ℝ)*X 0 1+(1127896217/2000000000 : ℝ)*X 0 2+(262256371/625000000 : ℝ)*X 1 0+(1559209861/5000000000 : ℝ)*X 1 1+(1127896217/2000000000 : ℝ)*X 1 2+(262256371/625000000 : ℝ)*X 2 0+(1559209861/5000000000 : ℝ)*X 2 1+(1127896217/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-234702819/1250000000 : ℝ)*X 0 0+(1205102363/2500000000 : ℝ)*X 0 1+(3003464269/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5172821483/10000000000 : ℝ)*X 1 0+(-1370782183/10000000000 : ℝ)*X 1 1+(1501732521/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1034564447/2000000000 : ℝ)*X 2 0+(3003464523/5000000000 : ℝ)*X 2 1+(-1370782703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4206104877/10000000000 : ℝ)*X 0 0+(222980521/400000000 : ℝ)*X 0 1+(1592840103/5000000000 : ℝ)*X 0 2+(4206104877/10000000000 : ℝ)*X 1 0+(222980521/400000000 : ℝ)*X 1 1+(1592840103/5000000000 : ℝ)*X 1 2+(4206104877/10000000000 : ℝ)*X 2 0+(222980521/400000000 : ℝ)*X 2 1+(1592840103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (88761952723077237278511/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (226581/625000000000 : ℝ)*(base1) + (1051106633/100000000000000 : ℝ)*(base19) + (15924093/1562500000000 : ℝ)*(base23) + (43793171/50000000000000 : ℝ)*(base24) + (132310377/50000000000000 : ℝ)*(upper3) + (18675962813571/3125000000000 : ℝ)*(major0) + (18675962813571/3125000000000 : ℝ)*(major1) + (597630810034273/100000000000000 : ℝ)*(major2) + (399299032531573/50000000000000 : ℝ)*(sp0) + (79859914252723/10000000000000 : ℝ)*(sp1) + (798599086905569/100000000000000 : ℝ)*(sp2) + (396659353333691/100000000000000 : ℝ)*(sp3) + (1082411839/50000000000000 : ℝ)*(sp4) + (1888911437/100000000000000 : ℝ)*(sp7) + (49582659812261/12500000000000 : ℝ)*(f.failure) + (798600193633863/100000000000000 : ℝ)*(f.sum) + (11827861882079/16000000000000000000000000000 : ℝ)*base66 + (969079839727163/80000000000000000000000000000 : ℝ)*base68 + (7813217174899/2500000000000000000000000000 : ℝ)*base69 + (284139257327163/80000000000000000000000000000 : ℝ)*base72 + (54089206682079/16000000000000000000000000000 : ℝ)*base74 + (1441579409899/2500000000000000000000000000 : ℝ)*base75 + (21573895980101/2500000000000000000000000000 : ℝ)*base78 + (12836656847601/2500000000000000000000000000 : ℝ)*base80 + (4287599477399/1250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2937259/312500000000000000000 : ℝ)*base89 + (2937259/312500000000000000000 : ℝ)*base91 + (187741/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (115717566890769395108841/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1546782373/100000000000000 : ℝ)*(base19) + (215897143/12500000000000 : ℝ)*(base23) + (4963023/12500000000000 : ℝ)*(base39) + (76883751/25000000000000 : ℝ)*(upper3) + (23677053/25000000000000 : ℝ)*(upper5) + (315353807795823/50000000000000 : ℝ)*(major0) + (315353807795823/50000000000000 : ℝ)*(major1) + (630707575887463/100000000000000 : ℝ)*(major2) + (90335971/2500000000000 : ℝ)*(sp1) + (976476999/25000000000000 : ℝ)*(sp2) + (42139994273773/5000000000000 : ℝ)*(sp4) + (421397362627123/50000000000000 : ℝ)*(sp5) + (421397146047251/50000000000000 : ℝ)*(sp6) + (418615113141031/100000000000000 : ℝ)*(sp7) + (418615113141031/100000000000000 : ℝ)*(f.failure) + (842799925179643/100000000000000 : ℝ)*(f.sum) + (15191005937479/80000000000000000000000000000 : ℝ)*base66 + (1044930730617053/80000000000000000000000000000 : ℝ)*base68 + (281031770579787/40000000000000000000000000000 : ℝ)*base69 + (164179965017053/80000000000000000000000000000 : ℝ)*base72 + (520379419537479/80000000000000000000000000000 : ℝ)*base74 + (357993195219787/40000000000000000000000000000 : ℝ)*base75 + (25253784740213/40000000000000000000000000000 : ℝ)*base78 + (49981324340213/40000000000000000000000000000 : ℝ)*base80 + (34855662579787/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (15634889/2500000000000000000000 : ℝ)*base89 + (15634889/2500000000000000000000 : ℝ)*base91 + (9365111/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1203_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (331/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27583/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1203_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1203_s1_0 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-259112263/1250000000 : ℝ)*x 0 + (177672339/312500000 : ℝ)*x 1 + (2507390523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259112263/1250000000 : ℝ)^2099 ≤ (12476461960493/100000000000000 : ℝ)^1587 := by
    have hnat : (259112263 : ℕ)^2099*100000000000000^1587 ≤ 12476461960493^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259112263 1250000000 12476461960493 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177672339/312500000 : ℝ)^2099 ≤ (11846588976589/25000000000000 : ℝ)^1587 := by
    have hnat : (177672339 : ℕ)^2099*25000000000000^1587 ≤ 11846588976589^1587*312500000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177672339 312500000 11846588976589 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2507390523/5000000000 : ℝ)^2099 ≤ (40137182119843/100000000000000 : ℝ)^1587 := by
    have hnat : (2507390523 : ℕ)^2099*100000000000000^1587 ≤ 40137182119843^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507390523 5000000000 40137182119843 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-259112263/1250000000 : ℝ), (177672339/312500000 : ℝ), (2507390523/5000000000 : ℝ)] ![(12476461960493/100000000000000 : ℝ), (11846588976589/25000000000000 : ℝ), (40137182119843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-259112263/1250000000 : ℝ)|^2099 ≤ (12476461960493/100000000000000 : ℝ)^1587
        have hw : |(-259112263/1250000000 : ℝ)|=(259112263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(177672339/312500000 : ℝ)|^2099 ≤ (11846588976589/25000000000000 : ℝ)^1587
        have hw : |(177672339/312500000 : ℝ)|=(177672339/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2507390523/5000000000 : ℝ)|^2099 ≤ (40137182119843/100000000000000 : ℝ)^1587
        have hw : |(2507390523/5000000000 : ℝ)|=(2507390523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s1_1 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5415782903/10000000000 : ℝ)*x 0 + (-243375623/1000000000 : ℝ)*x 1 + (5014781471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415782903/10000000000 : ℝ)^2099 ≤ (5554496605127/12500000000000 : ℝ)^1587 := by
    have hnat : (5415782903 : ℕ)^2099*12500000000000^1587 ≤ 5554496605127^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415782903 10000000000 5554496605127 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243375623/1000000000 : ℝ)^2099 ≤ (15426840522231/100000000000000 : ℝ)^1587 := by
    have hnat : (243375623 : ℕ)^2099*100000000000000^1587 ≤ 15426840522231^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243375623 1000000000 15426840522231 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5014781471/10000000000 : ℝ)^2099 ≤ (20068593309439/50000000000000 : ℝ)^1587 := by
    have hnat : (5014781471 : ℕ)^2099*50000000000000^1587 ≤ 20068593309439^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014781471 10000000000 20068593309439 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415782903/10000000000 : ℝ), (-243375623/1000000000 : ℝ), (5014781471/10000000000 : ℝ)] ![(5554496605127/12500000000000 : ℝ), (15426840522231/100000000000000 : ℝ), (20068593309439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415782903/10000000000 : ℝ)|^2099 ≤ (5554496605127/12500000000000 : ℝ)^1587
        have hw : |(5415782903/10000000000 : ℝ)|=(5415782903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-243375623/1000000000 : ℝ)|^2099 ≤ (15426840522231/100000000000000 : ℝ)^1587
        have hw : |(-243375623/1000000000 : ℝ)|=(243375623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5014781471/10000000000 : ℝ)|^2099 ≤ (20068593309439/50000000000000 : ℝ)^1587
        have hw : |(5014781471/10000000000 : ℝ)|=(5014781471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s1_2 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1083156347/2000000000 : ℝ)*x 0 + (5014782219/10000000000 : ℝ)*x 1 + (-1216878399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083156347/2000000000 : ℝ)^2099 ≤ (8887192033181/20000000000000 : ℝ)^1587 := by
    have hnat : (1083156347 : ℕ)^2099*20000000000000^1587 ≤ 8887192033181^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083156347 2000000000 8887192033181 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5014782219/10000000000 : ℝ)^2099 ≤ (40137194537179/100000000000000 : ℝ)^1587 := by
    have hnat : (5014782219 : ℕ)^2099*100000000000000^1587 ≤ 40137194537179^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014782219 10000000000 40137194537179 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216878399/5000000000 : ℝ)^2099 ≤ (1542684528417/10000000000000 : ℝ)^1587 := by
    have hnat : (1216878399 : ℕ)^2099*10000000000000^1587 ≤ 1542684528417^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216878399 5000000000 1542684528417 10000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083156347/2000000000 : ℝ), (5014782219/10000000000 : ℝ), (-1216878399/5000000000 : ℝ)] ![(8887192033181/20000000000000 : ℝ), (40137194537179/100000000000000 : ℝ), (1542684528417/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083156347/2000000000 : ℝ)|^2099 ≤ (8887192033181/20000000000000 : ℝ)^1587
        have hw : |(1083156347/2000000000 : ℝ)|=(1083156347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5014782219/10000000000 : ℝ)|^2099 ≤ (40137194537179/100000000000000 : ℝ)^1587
        have hw : |(5014782219/10000000000 : ℝ)|=(5014782219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1216878399/5000000000 : ℝ)|^2099 ≤ (1542684528417/10000000000000 : ℝ)^1587
        have hw : |(-1216878399/5000000000 : ℝ)|=(1216878399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s1_3 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (134757089/312500000 : ℝ)*x 0 + (3688354863/10000000000 : ℝ)*x 1 + (5038747563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134757089/312500000 : ℝ)^2099 ≤ (6574739506303/20000000000000 : ℝ)^1587 := by
    have hnat : (134757089 : ℕ)^2099*20000000000000^1587 ≤ 6574739506303^1587*312500000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134757089 312500000 6574739506303 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3688354863/10000000000 : ℝ)^2099 ≤ (6683804067017/25000000000000 : ℝ)^1587 := by
    have hnat : (3688354863 : ℕ)^2099*25000000000000^1587 ≤ 6683804067017^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688354863 10000000000 6683804067017 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5038747563/10000000000 : ℝ)^2099 ≤ (20195543094441/50000000000000 : ℝ)^1587 := by
    have hnat : (5038747563 : ℕ)^2099*50000000000000^1587 ≤ 20195543094441^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5038747563 10000000000 20195543094441 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134757089/312500000 : ℝ), (3688354863/10000000000 : ℝ), (5038747563/10000000000 : ℝ)] ![(6574739506303/20000000000000 : ℝ), (6683804067017/25000000000000 : ℝ), (20195543094441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134757089/312500000 : ℝ)|^2099 ≤ (6574739506303/20000000000000 : ℝ)^1587
        have hw : |(134757089/312500000 : ℝ)|=(134757089/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3688354863/10000000000 : ℝ)|^2099 ≤ (6683804067017/25000000000000 : ℝ)^1587
        have hw : |(3688354863/10000000000 : ℝ)|=(3688354863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5038747563/10000000000 : ℝ)|^2099 ≤ (20195543094441/50000000000000 : ℝ)^1587
        have hw : |(5038747563/10000000000 : ℝ)|=(5038747563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s1_4 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-259202629/1250000000 : ℝ)*x 0 + (5023726479/10000000000 : ℝ)*x 1 + (1135279507/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259202629/1250000000 : ℝ)^2099 ≤ (12482217267297/100000000000000 : ℝ)^1587 := by
    have hnat : (259202629 : ℕ)^2099*100000000000000^1587 ≤ 12482217267297^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259202629 1250000000 12482217267297 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5023726479/10000000000 : ℝ)^2099 ≤ (8046381077941/20000000000000 : ℝ)^1587 := by
    have hnat : (5023726479 : ℕ)^2099*20000000000000^1587 ≤ 8046381077941^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5023726479 10000000000 8046381077941 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135279507/2000000000 : ℝ)^2099 ≤ (23642938662761/50000000000000 : ℝ)^1587 := by
    have hnat : (1135279507 : ℕ)^2099*50000000000000^1587 ≤ 23642938662761^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135279507 2000000000 23642938662761 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-259202629/1250000000 : ℝ), (5023726479/10000000000 : ℝ), (1135279507/2000000000 : ℝ)] ![(12482217267297/100000000000000 : ℝ), (8046381077941/20000000000000 : ℝ), (23642938662761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-259202629/1250000000 : ℝ)|^2099 ≤ (12482217267297/100000000000000 : ℝ)^1587
        have hw : |(-259202629/1250000000 : ℝ)|=(259202629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5023726479/10000000000 : ℝ)|^2099 ≤ (8046381077941/20000000000000 : ℝ)^1587
        have hw : |(5023726479/10000000000 : ℝ)|=(5023726479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1135279507/2000000000 : ℝ)|^2099 ≤ (23642938662761/50000000000000 : ℝ)^1587
        have hw : |(1135279507/2000000000 : ℝ)|=(1135279507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s1_5 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5243302417/10000000000 : ℝ)*x 0 + (-1772141923/10000000000 : ℝ)*x 1 + (1419098961/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243302417/10000000000 : ℝ)^2099 ≤ (42573904177457/100000000000000 : ℝ)^1587 := by
    have hnat : (5243302417 : ℕ)^2099*100000000000000^1587 ≤ 42573904177457^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243302417 10000000000 42573904177457 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1772141923/10000000000 : ℝ)^2099 ≤ (10140237107303/100000000000000 : ℝ)^1587 := by
    have hnat : (1772141923 : ℕ)^2099*100000000000000^1587 ≤ 10140237107303^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772141923 10000000000 10140237107303 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1419098961/2500000000 : ℝ)^2099 ≤ (9457171738891/20000000000000 : ℝ)^1587 := by
    have hnat : (1419098961 : ℕ)^2099*20000000000000^1587 ≤ 9457171738891^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419098961 2500000000 9457171738891 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243302417/10000000000 : ℝ), (-1772141923/10000000000 : ℝ), (1419098961/2500000000 : ℝ)] ![(42573904177457/100000000000000 : ℝ), (10140237107303/100000000000000 : ℝ), (9457171738891/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243302417/10000000000 : ℝ)|^2099 ≤ (42573904177457/100000000000000 : ℝ)^1587
        have hw : |(5243302417/10000000000 : ℝ)|=(5243302417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1772141923/10000000000 : ℝ)|^2099 ≤ (10140237107303/100000000000000 : ℝ)^1587
        have hw : |(-1772141923/10000000000 : ℝ)|=(1772141923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1419098961/2500000000 : ℝ)|^2099 ≤ (9457171738891/20000000000000 : ℝ)^1587
        have hw : |(1419098961/2500000000 : ℝ)|=(1419098961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s1_6 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (327706407/625000000 : ℝ)*x 0 + (5676396349/10000000000 : ℝ)*x 1 + (-1772141053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327706407/625000000 : ℝ)^2099 ≤ (21286952598843/50000000000000 : ℝ)^1587 := by
    have hnat : (327706407 : ℕ)^2099*50000000000000^1587 ≤ 21286952598843^1587*625000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327706407 625000000 21286952598843 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5676396349/10000000000 : ℝ)^2099 ≤ (23642932129217/50000000000000 : ℝ)^1587 := by
    have hnat : (5676396349 : ℕ)^2099*50000000000000^1587 ≤ 23642932129217^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5676396349 10000000000 23642932129217 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1772141053/10000000000 : ℝ)^2099 ≤ (10140230523083/100000000000000 : ℝ)^1587 := by
    have hnat : (1772141053 : ℕ)^2099*100000000000000^1587 ≤ 10140230523083^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772141053 10000000000 10140230523083 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327706407/625000000 : ℝ), (5676396349/10000000000 : ℝ), (-1772141053/10000000000 : ℝ)] ![(21286952598843/50000000000000 : ℝ), (23642932129217/50000000000000 : ℝ), (10140230523083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327706407/625000000 : ℝ)|^2099 ≤ (21286952598843/50000000000000 : ℝ)^1587
        have hw : |(327706407/625000000 : ℝ)|=(327706407/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5676396349/10000000000 : ℝ)|^2099 ≤ (23642932129217/50000000000000 : ℝ)^1587
        have hw : |(5676396349/10000000000 : ℝ)|=(5676396349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1772141053/10000000000 : ℝ)|^2099 ≤ (10140230523083/100000000000000 : ℝ)^1587
        have hw : |(-1772141053/10000000000 : ℝ)|=(1772141053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s1_7 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (539210551/1250000000 : ℝ)*x 0 + (5020736363/10000000000 : ℝ)*x 1 + (926678509/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539210551/1250000000 : ℝ)^2099 ≤ (32888394663219/100000000000000 : ℝ)^1587 := by
    have hnat : (539210551 : ℕ)^2099*100000000000000^1587 ≤ 32888394663219^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539210551 1250000000 32888394663219 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5020736363/10000000000 : ℝ)^2099 ≤ (40200236965109/100000000000000 : ℝ)^1587 := by
    have hnat : (5020736363 : ℕ)^2099*100000000000000^1587 ≤ 40200236965109^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020736363 10000000000 40200236965109 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (926678509/2500000000 : ℝ)^2099 ≤ (13455684181199/50000000000000 : ℝ)^1587 := by
    have hnat : (926678509 : ℕ)^2099*50000000000000^1587 ≤ 13455684181199^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926678509 2500000000 13455684181199 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539210551/1250000000 : ℝ), (5020736363/10000000000 : ℝ), (926678509/2500000000 : ℝ)] ![(32888394663219/100000000000000 : ℝ), (40200236965109/100000000000000 : ℝ), (13455684181199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539210551/1250000000 : ℝ)|^2099 ≤ (32888394663219/100000000000000 : ℝ)^1587
        have hw : |(539210551/1250000000 : ℝ)|=(539210551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5020736363/10000000000 : ℝ)|^2099 ≤ (40200236965109/100000000000000 : ℝ)^1587
        have hw : |(5020736363/10000000000 : ℝ)|=(5020736363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(926678509/2500000000 : ℝ)|^2099 ≤ (13455684181199/50000000000000 : ℝ)^1587
        have hw : |(926678509/2500000000 : ℝ)|=(926678509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1203_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27583/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (331/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (187/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10083/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27583/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (331/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27583/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (331/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27583/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (331/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27583/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (331/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27583/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (331/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27583/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (331/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (331/50000 : ℝ) ^ (8395/2048 : ℝ) ≤ (116797357799/100000000000000000000 : ℝ) := by
    have hpowers : (331/50000 : ℝ)^8395 ≤ (116797357799/100000000000000000000 : ℝ)^2048 := by
      have hnat : (331 : ℕ)^8395*100000000000000000000^2048 ≤ 116797357799^2048*50000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        331 50000 116797357799 100000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (331/50000 : ℝ)) (X := (116797357799/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27583/100000 : ℝ) ^ (8395/2048 : ℝ) ≤ (127368425442349571/25000000000000000000 : ℝ) := by
    have hpowers : (27583/100000 : ℝ)^8395 ≤ (127368425442349571/25000000000000000000 : ℝ)^2048 := by
      have hnat : (27583 : ℕ)^8395*25000000000000000000^2048 ≤ 127368425442349571^2048*100000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27583 100000 127368425442349571 25000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27583/100000 : ℝ)) (X := (127368425442349571/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000116797357799/50000000000000000000 : ℝ) ≤ (5000000002849327/5000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (50000000116797357799/50000000000000000000 : ℝ)^2048 ≤ (5000000002849327/5000000000000000 : ℝ)^8395 := by
      have hnat : (50000000116797357799 : ℕ)^2048*5000000000000000^8395 ≤ 5000000002849327^8395*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000116797357799 50000000000000000000 5000000002849327 5000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000002849327/5000000000000000 : ℝ)) (X := (50000000116797357799/50000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100509473818566756083/100000000000000000000 : ℝ) ≤ (2503101247278477/2500000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (100509473818566756083/100000000000000000000 : ℝ)^2048 ≤ (2503101247278477/2500000000000000 : ℝ)^8395 := by
      have hnat : (100509473818566756083 : ℕ)^2048*2500000000000000^8395 ≤ 2503101247278477^8395*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100509473818566756083 100000000000000000000 2503101247278477 2500000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503101247278477/2500000000000000 : ℝ)) (X := (100509473818566756083/100000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12627368425442349571/12500000000000000000 : ℝ) ≤ (5012404986264581/5000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (12627368425442349571/12500000000000000000 : ℝ)^2048 ≤ (5012404986264581/5000000000000000 : ℝ)^8395 := by
      have hnat : (12627368425442349571 : ℕ)^2048*5000000000000000^8395 ≤ 5012404986264581^8395*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12627368425442349571 12500000000000000000 5012404986264581 5000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012404986264581/5000000000000000 : ℝ)) (X := (12627368425442349571/12500000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(116797357799/100000000000000000000 : ℝ) ≤ ((134596787977685834019/134605000000000000000 : ℝ)+2*(6202491707627/1346050000000000 : ℝ)*(331/50000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (134596787977685834019/134605000000000000000 : ℝ)+2*(6202491707627/1346050000000000 : ℝ)*(331/50000 : ℝ)=(5000000002849327/5000000000000000 : ℝ) by norm_num, show 1+2*(116797357799/100000000000000000000 : ℝ)=(50000000116797357799/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(127368425442349571/25000000000000000000 : ℝ)+(116797357799/100000000000000000000 : ℝ) ≤ ((134596787977685834019/134605000000000000000 : ℝ)+(6202491707627/1346050000000000 : ℝ)*((27583/100000 : ℝ)+(331/50000 : ℝ)))^(8395/2048 : ℝ) := by
    rw [show (134596787977685834019/134605000000000000000 : ℝ)+(6202491707627/1346050000000000 : ℝ)*((27583/100000 : ℝ)+(331/50000 : ℝ))=(2503101247278477/2500000000000000 : ℝ) by norm_num, show 1+(127368425442349571/25000000000000000000 : ℝ)+(116797357799/100000000000000000000 : ℝ)=(100509473818566756083/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(127368425442349571/25000000000000000000 : ℝ) ≤ ((134596787977685834019/134605000000000000000 : ℝ)+2*(6202491707627/1346050000000000 : ℝ)*(27583/100000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (134596787977685834019/134605000000000000000 : ℝ)+2*(6202491707627/1346050000000000 : ℝ)*(27583/100000 : ℝ)=(5012404986264581/5000000000000000 : ℝ) by norm_num, show 1+2*(127368425442349571/25000000000000000000 : ℝ)=(12627368425442349571/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (134596787977685834019/134605000000000000000 : ℝ)*(X 1 0+X 2 0)+(6202491707627/1346050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (331/50000 : ℝ)) (hi := (27583/100000 : ℝ)) (c := (134596787977685834019/134605000000000000000 : ℝ)) (alpha := (6202491707627/1346050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (134596787977685834019/134605000000000000000 : ℝ)*(X 0 1+X 2 1)+(6202491707627/1346050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (331/50000 : ℝ)) (hi := (27583/100000 : ℝ)) (c := (134596787977685834019/134605000000000000000 : ℝ)) (alpha := (6202491707627/1346050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (134596787977685834019/134605000000000000000 : ℝ)*(X 0 2+X 1 2)+(6202491707627/1346050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (331/50000 : ℝ)) (hi := (27583/100000 : ℝ)) (c := (134596787977685834019/134605000000000000000 : ℝ)) (alpha := (6202491707627/1346050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-259112263/1250000000 : ℝ)*X 0 0+(177672339/312500000 : ℝ)*X 0 1+(2507390523/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5415782903/10000000000 : ℝ)*X 1 0+(-243375623/1000000000 : ℝ)*X 1 1+(5014781471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1083156347/2000000000 : ℝ)*X 2 0+(5014782219/10000000000 : ℝ)*X 2 1+(-1216878399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((134757089/312500000 : ℝ)*X 0 0+(3688354863/10000000000 : ℝ)*X 0 1+(5038747563/10000000000 : ℝ)*X 0 2+(134757089/312500000 : ℝ)*X 1 0+(3688354863/10000000000 : ℝ)*X 1 1+(5038747563/10000000000 : ℝ)*X 1 2+(134757089/312500000 : ℝ)*X 2 0+(3688354863/10000000000 : ℝ)*X 2 1+(5038747563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-259202629/1250000000 : ℝ)*X 0 0+(5023726479/10000000000 : ℝ)*X 0 1+(1135279507/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5243302417/10000000000 : ℝ)*X 1 0+(-1772141923/10000000000 : ℝ)*X 1 1+(1419098961/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((327706407/625000000 : ℝ)*X 2 0+(5676396349/10000000000 : ℝ)*X 2 1+(-1772141053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((539210551/1250000000 : ℝ)*X 0 0+(5020736363/10000000000 : ℝ)*X 0 1+(926678509/2500000000 : ℝ)*X 0 2+(539210551/1250000000 : ℝ)*X 1 0+(5020736363/10000000000 : ℝ)*X 1 1+(926678509/2500000000 : ℝ)*X 1 2+(539210551/1250000000 : ℝ)*X 2 0+(5020736363/10000000000 : ℝ)*X 2 1+(926678509/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7967628786955391717709/1346050000000000000000000000 : ℝ) := by norm_num
    linear_combination (1543014567/100000000000000 : ℝ)*(base19) + (1161062923/100000000000000 : ℝ)*(base23) + (1469579/50000000000000 : ℝ)*(upper2) + (341781659/100000000000000 : ℝ)*(upper3) + (17828103/50000000000000 : ℝ)*(upper4) + (111572909058489/10000000000000 : ℝ)*(major0) + (111572909058489/10000000000000 : ℝ)*(major1) + (111572909058489/10000000000000 : ℝ)*(major2) + (745457786428971/50000000000000 : ℝ)*(sp0) + (745460724087479/50000000000000 : ℝ)*(sp1) + (745460915063301/50000000000000 : ℝ)*(sp2) + (185132369854627/25000000000000 : ℝ)*(sp3) + (115911431/1562500000000 : ℝ)*(sp4) + (689156607/12500000000000 : ℝ)*(sp7) + (185133748167841/25000000000000 : ℝ)*(f.failure) + (59636919647581/4000000000000 : ℝ)*(f.sum) + (9452826523721/6730250000000000000000000000 : ℝ)*base66 + (3238218467220962709/1346050000000000000000000000000000 : ℝ)*base68 + (11358605519034362709/1346050000000000000000000000000000 : ℝ)*base70 + (3452629389145937291/1346050000000000000000000000000000 : ℝ)*base71 + (1372825230851/1346050000000000000000000000 : ℝ)*base74 + (3014260031127337291/1346050000000000000000000000000000 : ℝ)*base75 + (4300714713439862709/1346050000000000000000000000000000 : ℝ)*base78 + (12039510566108737291/1346050000000000000000000000000000 : ℝ)*base79 + (31173275178523/6730250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2147279/625000000000000000000 : ℝ)*base89 + (2147279/625000000000000000000 : ℝ)*base91 + (2147279/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (410977036486987520910226077/105160156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (162873659/25000000000000 : ℝ)*(base19) + (166813663/20000000000000 : ℝ)*(base23) + (74841777/50000000000000 : ℝ)*(base32) + (19620073/50000000000000 : ℝ)*(lower4) + (143324322054069/12500000000000 : ℝ)*(major0) + (143324322054069/12500000000000 : ℝ)*(major1) + (143324322054069/12500000000000 : ℝ)*(major2) + (48213249/4000000000000 : ℝ)*(sp0) + (193348281/12500000000000 : ℝ)*(sp1) + (3977998707/100000000000000 : ℝ)*(sp2) + (76608334678461/5000000000000 : ℝ)*(sp4) + (766082850309781/50000000000000 : ℝ)*(sp5) + (95760192927089/6250000000000 : ℝ)*(sp6) + (761020974010901/100000000000000 : ℝ)*(sp7) + (152204224738891/20000000000000 : ℝ)*(f.failure) + (306433579780089/20000000000000 : ℝ)*(f.sum) + (23806152878777/8412812500000000000000000000 : ℝ)*base66 + (4749899655166185811/1682562500000000000000000000000000 : ℝ)*base67 + (336053090071501689/1682562500000000000000000000000000 : ℝ)*base70 + (6310816408622751689/1682562500000000000000000000000000 : ℝ)*base72 + (152773883620523/134605000000000000000000000000 : ℝ)*base73 + (7046242042084376689/1682562500000000000000000000000000 : ℝ)*base76 + (8099344061662439189/1682562500000000000000000000000000 : ℝ)*base78 + (3670408036540626689/1682562500000000000000000000000000 : ℝ)*base80 + (93372714387759/67302500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (112229/500000000000000000000 : ℝ)*base89 + (112229/500000000000000000000 : ℝ)*base91 + (112229/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1203_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27583/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (331/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (187/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10083/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1203_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1203_s2_0 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-53073097/250000000 : ℝ)*x 0 + (2749789393/5000000000 : ℝ)*x 1 + (5168849439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53073097/250000000 : ℝ)^2099 ≤ (12876242047103/100000000000000 : ℝ)^1587 := by
    have hnat : (53073097 : ℕ)^2099*100000000000000^1587 ≤ 12876242047103^1587*250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53073097 250000000 12876242047103 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2749789393/5000000000 : ℝ)^2099 ≤ (22673792893993/50000000000000 : ℝ)^1587 := by
    have hnat : (2749789393 : ℕ)^2099*50000000000000^1587 ≤ 22673792893993^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749789393 5000000000 22673792893993 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5168849439/10000000000 : ℝ)^2099 ≤ (8355234431163/20000000000000 : ℝ)^1587 := by
    have hnat : (5168849439 : ℕ)^2099*20000000000000^1587 ≤ 8355234431163^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168849439 10000000000 8355234431163 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53073097/250000000 : ℝ), (2749789393/5000000000 : ℝ), (5168849439/10000000000 : ℝ)] ![(12876242047103/100000000000000 : ℝ), (22673792893993/50000000000000 : ℝ), (8355234431163/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53073097/250000000 : ℝ)|^2099 ≤ (12876242047103/100000000000000 : ℝ)^1587
        have hw : |(-53073097/250000000 : ℝ)|=(53073097/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2749789393/5000000000 : ℝ)|^2099 ≤ (22673792893993/50000000000000 : ℝ)^1587
        have hw : |(2749789393/5000000000 : ℝ)|=(2749789393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5168849439/10000000000 : ℝ)|^2099 ≤ (8355234431163/20000000000000 : ℝ)^1587
        have hw : |(5168849439/10000000000 : ℝ)|=(5168849439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s2_1 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5371284869/10000000000 : ℝ)*x 0 + (-35851143/156250000 : ℝ)*x 1 + (5168854021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371284869/10000000000 : ℝ)^2099 ≤ (5494215288241/12500000000000 : ℝ)^1587 := by
    have hnat : (5371284869 : ℕ)^2099*12500000000000^1587 ≤ 5494215288241^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371284869 10000000000 5494215288241 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35851143/156250000 : ℝ)^2099 ≤ (14270056530159/100000000000000 : ℝ)^1587 := by
    have hnat : (35851143 : ℕ)^2099*100000000000000^1587 ≤ 14270056530159^1587*156250000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35851143 156250000 14270056530159 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5168854021/10000000000 : ℝ)^2099 ≤ (10444055284141/25000000000000 : ℝ)^1587 := by
    have hnat : (5168854021 : ℕ)^2099*25000000000000^1587 ≤ 10444055284141^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168854021 10000000000 10444055284141 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371284869/10000000000 : ℝ), (-35851143/156250000 : ℝ), (5168854021/10000000000 : ℝ)] ![(5494215288241/12500000000000 : ℝ), (14270056530159/100000000000000 : ℝ), (10444055284141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371284869/10000000000 : ℝ)|^2099 ≤ (5494215288241/12500000000000 : ℝ)^1587
        have hw : |(5371284869/10000000000 : ℝ)|=(5371284869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35851143/156250000 : ℝ)|^2099 ≤ (14270056530159/100000000000000 : ℝ)^1587
        have hw : |(-35851143/156250000 : ℝ)|=(35851143/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5168854021/10000000000 : ℝ)|^2099 ≤ (10444055284141/25000000000000 : ℝ)^1587
        have hw : |(5168854021/10000000000 : ℝ)|=(5168854021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s2_2 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074257379/2000000000 : ℝ)*x 0 + (2584425603/5000000000 : ℝ)*x 1 + (-458894829/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074257379/2000000000 : ℝ)^2099 ≤ (10988436058399/25000000000000 : ℝ)^1587 := by
    have hnat : (1074257379 : ℕ)^2099*25000000000000^1587 ≤ 10988436058399^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074257379 2000000000 10988436058399 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2584425603/5000000000 : ℝ)^2099 ≤ (41776191044723/100000000000000 : ℝ)^1587 := by
    have hnat : (2584425603 : ℕ)^2099*100000000000000^1587 ≤ 41776191044723^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584425603 5000000000 41776191044723 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458894829/2000000000 : ℝ)^2099 ≤ (14270064698381/100000000000000 : ℝ)^1587 := by
    have hnat : (458894829 : ℕ)^2099*100000000000000^1587 ≤ 14270064698381^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458894829 2000000000 14270064698381 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074257379/2000000000 : ℝ), (2584425603/5000000000 : ℝ), (-458894829/2000000000 : ℝ)] ![(10988436058399/25000000000000 : ℝ), (41776191044723/100000000000000 : ℝ), (14270064698381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074257379/2000000000 : ℝ)|^2099 ≤ (10988436058399/25000000000000 : ℝ)^1587
        have hw : |(1074257379/2000000000 : ℝ)|=(1074257379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2584425603/5000000000 : ℝ)|^2099 ≤ (41776191044723/100000000000000 : ℝ)^1587
        have hw : |(2584425603/5000000000 : ℝ)|=(2584425603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-458894829/2000000000 : ℝ)|^2099 ≤ (14270064698381/100000000000000 : ℝ)^1587
        have hw : |(-458894829/2000000000 : ℝ)|=(458894829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s2_3 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (869338261/2000000000 : ℝ)*x 0 + (805244633/2000000000 : ℝ)*x 1 + (1173019689/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869338261/2000000000 : ℝ)^2099 ≤ (33221644013911/100000000000000 : ℝ)^1587 := by
    have hnat : (869338261 : ℕ)^2099*100000000000000^1587 ≤ 33221644013911^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869338261 2000000000 33221644013911 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805244633/2000000000 : ℝ)^2099 ≤ (150106492457/500000000000 : ℝ)^1587 := by
    have hnat : (805244633 : ℕ)^2099*500000000000^1587 ≤ 150106492457^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805244633 2000000000 150106492457 500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1173019689/2500000000 : ℝ)^2099 ≤ (2297316092059/6250000000000 : ℝ)^1587 := by
    have hnat : (1173019689 : ℕ)^2099*6250000000000^1587 ≤ 2297316092059^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173019689 2500000000 2297316092059 6250000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869338261/2000000000 : ℝ), (805244633/2000000000 : ℝ), (1173019689/2500000000 : ℝ)] ![(33221644013911/100000000000000 : ℝ), (150106492457/500000000000 : ℝ), (2297316092059/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869338261/2000000000 : ℝ)|^2099 ≤ (33221644013911/100000000000000 : ℝ)^1587
        have hw : |(869338261/2000000000 : ℝ)|=(869338261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805244633/2000000000 : ℝ)|^2099 ≤ (150106492457/500000000000 : ℝ)^1587
        have hw : |(805244633/2000000000 : ℝ)|=(805244633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1173019689/2500000000 : ℝ)|^2099 ≤ (2297316092059/6250000000000 : ℝ)^1587
        have hw : |(1173019689/2500000000 : ℝ)|=(1173019689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s2_4 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-84920387/400000000 : ℝ)*x 0 + (1292758953/2500000000 : ℝ)*x 1 + (5497372327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84920387/400000000 : ℝ)^2099 ≤ (6438465155533/50000000000000 : ℝ)^1587 := by
    have hnat : (84920387 : ℕ)^2099*50000000000000^1587 ≤ 6438465155533^1587*400000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84920387 400000000 6438465155533 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292758953/2500000000 : ℝ)^2099 ≤ (20899772838923/50000000000000 : ℝ)^1587 := by
    have hnat : (1292758953 : ℕ)^2099*50000000000000^1587 ≤ 20899772838923^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292758953 2500000000 20899772838923 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5497372327/10000000000 : ℝ)^2099 ≤ (22661761996939/50000000000000 : ℝ)^1587 := by
    have hnat : (5497372327 : ℕ)^2099*50000000000000^1587 ≤ 22661761996939^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497372327 10000000000 22661761996939 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84920387/400000000 : ℝ), (1292758953/2500000000 : ℝ), (5497372327/10000000000 : ℝ)] ![(6438465155533/50000000000000 : ℝ), (20899772838923/50000000000000 : ℝ), (22661761996939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84920387/400000000 : ℝ)|^2099 ≤ (6438465155533/50000000000000 : ℝ)^1587
        have hw : |(-84920387/400000000 : ℝ)|=(84920387/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1292758953/2500000000 : ℝ)|^2099 ≤ (20899772838923/50000000000000 : ℝ)^1587
        have hw : |(1292758953/2500000000 : ℝ)|=(1292758953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5497372327/10000000000 : ℝ)|^2099 ≤ (22661761996939/50000000000000 : ℝ)^1587
        have hw : |(5497372327/10000000000 : ℝ)|=(5497372327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s2_5 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643517789/5000000000 : ℝ)*x 0 + (-491488289/2500000000 : ℝ)*x 1 + (109947447/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643517789/5000000000 : ℝ)^2099 ≤ (1345131137191/3125000000000 : ℝ)^1587 := by
    have hnat : (2643517789 : ℕ)^2099*3125000000000^1587 ≤ 1345131137191^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643517789 5000000000 1345131137191 3125000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (491488289/2500000000 : ℝ)^2099 ≤ (11632279344911/100000000000000 : ℝ)^1587 := by
    have hnat : (491488289 : ℕ)^2099*100000000000000^1587 ≤ 11632279344911^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491488289 2500000000 11632279344911 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109947447/200000000 : ℝ)^2099 ≤ (1133088106117/2500000000000 : ℝ)^1587 := by
    have hnat : (109947447 : ℕ)^2099*2500000000000^1587 ≤ 1133088106117^1587*200000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109947447 200000000 1133088106117 2500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643517789/5000000000 : ℝ), (-491488289/2500000000 : ℝ), (109947447/200000000 : ℝ)] ![(1345131137191/3125000000000 : ℝ), (11632279344911/100000000000000 : ℝ), (1133088106117/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643517789/5000000000 : ℝ)|^2099 ≤ (1345131137191/3125000000000 : ℝ)^1587
        have hw : |(2643517789/5000000000 : ℝ)|=(2643517789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-491488289/2500000000 : ℝ)|^2099 ≤ (11632279344911/100000000000000 : ℝ)^1587
        have hw : |(-491488289/2500000000 : ℝ)|=(491488289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109947447/200000000 : ℝ)|^2099 ≤ (1133088106117/2500000000000 : ℝ)^1587
        have hw : |(109947447/200000000 : ℝ)|=(109947447/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s2_6 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5287035753/10000000000 : ℝ)*x 0 + (5497372373/10000000000 : ℝ)*x 1 + (-491488221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287035753/10000000000 : ℝ)^2099 ≤ (1721767930981/4000000000000 : ℝ)^1587 := by
    have hnat : (5287035753 : ℕ)^2099*4000000000000^1587 ≤ 1721767930981^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287035753 10000000000 1721767930981 4000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497372373/10000000000 : ℝ)^2099 ≤ (45323524495483/100000000000000 : ℝ)^1587 := by
    have hnat : (5497372373 : ℕ)^2099*100000000000000^1587 ≤ 45323524495483^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497372373 10000000000 45323524495483 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491488221/2500000000 : ℝ)^2099 ≤ (11632277216301/100000000000000 : ℝ)^1587 := by
    have hnat : (491488221 : ℕ)^2099*100000000000000^1587 ≤ 11632277216301^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491488221 2500000000 11632277216301 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287035753/10000000000 : ℝ), (5497372373/10000000000 : ℝ), (-491488221/2500000000 : ℝ)] ![(1721767930981/4000000000000 : ℝ), (45323524495483/100000000000000 : ℝ), (11632277216301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287035753/10000000000 : ℝ)|^2099 ≤ (1721767930981/4000000000000 : ℝ)^1587
        have hw : |(5287035753/10000000000 : ℝ)|=(5287035753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497372373/10000000000 : ℝ)|^2099 ≤ (45323524495483/100000000000000 : ℝ)^1587
        have hw : |(5497372373/10000000000 : ℝ)|=(5497372373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-491488221/2500000000 : ℝ)|^2099 ≤ (11632277216301/100000000000000 : ℝ)^1587
        have hw : |(-491488221/2500000000 : ℝ)|=(491488221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s2_7 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2173433221/5000000000 : ℝ)*x 0 + (2343839821/5000000000 : ℝ)*x 1 + (2015331967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173433221/5000000000 : ℝ)^2099 ≤ (16611707221553/50000000000000 : ℝ)^1587 := by
    have hnat : (2173433221 : ℕ)^2099*50000000000000^1587 ≤ 16611707221553^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173433221 5000000000 16611707221553 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2343839821/5000000000 : ℝ)^2099 ≤ (36711484173541/100000000000000 : ℝ)^1587 := by
    have hnat : (2343839821 : ℕ)^2099*100000000000000^1587 ≤ 36711484173541^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2343839821 5000000000 36711484173541 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015331967/5000000000 : ℝ)^2099 ≤ (30065101361433/100000000000000 : ℝ)^1587 := by
    have hnat : (2015331967 : ℕ)^2099*100000000000000^1587 ≤ 30065101361433^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015331967 5000000000 30065101361433 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173433221/5000000000 : ℝ), (2343839821/5000000000 : ℝ), (2015331967/5000000000 : ℝ)] ![(16611707221553/50000000000000 : ℝ), (36711484173541/100000000000000 : ℝ), (30065101361433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173433221/5000000000 : ℝ)|^2099 ≤ (16611707221553/50000000000000 : ℝ)^1587
        have hw : |(2173433221/5000000000 : ℝ)|=(2173433221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2343839821/5000000000 : ℝ)|^2099 ≤ (36711484173541/100000000000000 : ℝ)^1587
        have hw : |(2343839821/5000000000 : ℝ)|=(2343839821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015331967/5000000000 : ℝ)|^2099 ≤ (30065101361433/100000000000000 : ℝ)^1587
        have hw : |(2015331967/5000000000 : ℝ)|=(2015331967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1203_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10083/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (187/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (9337/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2041/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10083/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (187/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10083/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (187/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10083/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (187/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10083/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (187/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10083/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (187/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10083/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (187/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (187/3125 : ℝ) ^ (8395/2048 : ℝ) ≤ (969930034292359/100000000000000000000 : ℝ) := by
    have hpowers : (187/3125 : ℝ)^8395 ≤ (969930034292359/100000000000000000000 : ℝ)^2048 := by
      have hnat : (187 : ℕ)^8395*100000000000000000000^2048 ≤ 969930034292359^2048*3125^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        187 3125 969930034292359 100000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (187/3125 : ℝ)) (X := (969930034292359/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10083/50000 : ℝ) ^ (8395/2048 : ℝ) ≤ (28221636735989413/20000000000000000000 : ℝ) := by
    have hpowers : (10083/50000 : ℝ)^8395 ≤ (28221636735989413/20000000000000000000 : ℝ)^2048 := by
      have hnat : (10083 : ℕ)^8395*20000000000000000000^2048 ≤ 28221636735989413^2048*50000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10083 50000 28221636735989413 20000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10083/50000 : ℝ)) (X := (28221636735989413/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000969930034292359/50000000000000000000 : ℝ) ≤ (10000047323457863/10000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (50000969930034292359/50000000000000000000 : ℝ)^2048 ≤ (10000047323457863/10000000000000000 : ℝ)^8395 := by
      have hnat : (50000969930034292359 : ℕ)^2048*10000000000000000^8395 ≤ 10000047323457863^8395*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000969930034292359 50000000000000000000 10000047323457863 10000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000047323457863/10000000000000000 : ℝ)) (X := (50000969930034292359/50000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1564719970526784991/1562500000000000000 : ℝ) ≤ (1000346420282539/1000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (1564719970526784991/1562500000000000000 : ℝ)^2048 ≤ (1000346420282539/1000000000000000 : ℝ)^8395 := by
      have hnat : (1564719970526784991 : ℕ)^2048*1000000000000000^8395 ≤ 1000346420282539^8395*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1564719970526784991 1562500000000000000 1000346420282539 1000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000346420282539/1000000000000000 : ℝ)) (X := (1564719970526784991/1562500000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10028221636735989413/10000000000000000000 : ℝ) ≤ (10006881082192917/10000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (10028221636735989413/10000000000000000000 : ℝ)^2048 ≤ (10006881082192917/10000000000000000 : ℝ)^8395 := by
      have hnat : (10028221636735989413 : ℕ)^2048*10000000000000000^8395 ≤ 10006881082192917^8395*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10028221636735989413 10000000000000000000 10006881082192917 10000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006881082192917/10000000000000000 : ℝ)) (X := (10028221636735989413/10000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(969930034292359/100000000000000000000 : ℝ) ≤ ((14177977792900884993/14182000000000000000 : ℝ)+2*(3416879367527/1418200000000000 : ℝ)*(187/3125 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (14177977792900884993/14182000000000000000 : ℝ)+2*(3416879367527/1418200000000000 : ℝ)*(187/3125 : ℝ)=(10000047323457863/10000000000000000 : ℝ) by norm_num, show 1+2*(969930034292359/100000000000000000000 : ℝ)=(50000969930034292359/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28221636735989413/20000000000000000000 : ℝ)+(969930034292359/100000000000000000000 : ℝ) ≤ ((14177977792900884993/14182000000000000000 : ℝ)+(3416879367527/1418200000000000 : ℝ)*((10083/50000 : ℝ)+(187/3125 : ℝ)))^(8395/2048 : ℝ) := by
    rw [show (14177977792900884993/14182000000000000000 : ℝ)+(3416879367527/1418200000000000 : ℝ)*((10083/50000 : ℝ)+(187/3125 : ℝ))=(1000346420282539/1000000000000000 : ℝ) by norm_num, show 1+(28221636735989413/20000000000000000000 : ℝ)+(969930034292359/100000000000000000000 : ℝ)=(1564719970526784991/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28221636735989413/20000000000000000000 : ℝ) ≤ ((14177977792900884993/14182000000000000000 : ℝ)+2*(3416879367527/1418200000000000 : ℝ)*(10083/50000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (14177977792900884993/14182000000000000000 : ℝ)+2*(3416879367527/1418200000000000 : ℝ)*(10083/50000 : ℝ)=(10006881082192917/10000000000000000 : ℝ) by norm_num, show 1+2*(28221636735989413/20000000000000000000 : ℝ)=(10028221636735989413/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14177977792900884993/14182000000000000000 : ℝ)*(X 1 0+X 2 0)+(3416879367527/1418200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (187/3125 : ℝ)) (hi := (10083/50000 : ℝ)) (c := (14177977792900884993/14182000000000000000 : ℝ)) (alpha := (3416879367527/1418200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14177977792900884993/14182000000000000000 : ℝ)*(X 0 1+X 2 1)+(3416879367527/1418200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (187/3125 : ℝ)) (hi := (10083/50000 : ℝ)) (c := (14177977792900884993/14182000000000000000 : ℝ)) (alpha := (3416879367527/1418200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14177977792900884993/14182000000000000000 : ℝ)*(X 0 2+X 1 2)+(3416879367527/1418200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (187/3125 : ℝ)) (hi := (10083/50000 : ℝ)) (c := (14177977792900884993/14182000000000000000 : ℝ)) (alpha := (3416879367527/1418200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-53073097/250000000 : ℝ)*X 0 0+(2749789393/5000000000 : ℝ)*X 0 1+(5168849439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5371284869/10000000000 : ℝ)*X 1 0+(-35851143/156250000 : ℝ)*X 1 1+(5168854021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1074257379/2000000000 : ℝ)*X 2 0+(2584425603/5000000000 : ℝ)*X 2 1+(-458894829/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869338261/2000000000 : ℝ)*X 0 0+(805244633/2000000000 : ℝ)*X 0 1+(1173019689/2500000000 : ℝ)*X 0 2+(869338261/2000000000 : ℝ)*X 1 0+(805244633/2000000000 : ℝ)*X 1 1+(1173019689/2500000000 : ℝ)*X 1 2+(869338261/2000000000 : ℝ)*X 2 0+(805244633/2000000000 : ℝ)*X 2 1+(1173019689/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-84920387/400000000 : ℝ)*X 0 0+(1292758953/2500000000 : ℝ)*X 0 1+(5497372327/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643517789/5000000000 : ℝ)*X 1 0+(-491488289/2500000000 : ℝ)*X 1 1+(109947447/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287035753/10000000000 : ℝ)*X 2 0+(5497372373/10000000000 : ℝ)*X 2 1+(-491488221/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173433221/5000000000 : ℝ)*X 0 0+(2343839821/5000000000 : ℝ)*X 0 1+(2015331967/5000000000 : ℝ)*X 0 2+(2173433221/5000000000 : ℝ)*X 1 0+(2343839821/5000000000 : ℝ)*X 1 1+(2015331967/5000000000 : ℝ)*X 1 2+(2173433221/5000000000 : ℝ)*X 2 0+(2343839821/5000000000 : ℝ)*X 2 1+(2015331967/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (110886993985262285967755991/12662500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (209702591/12500000000000 : ℝ)*(base19) + (2372003871/100000000000000 : ℝ)*(base23) + (15718887/25000000000000 : ℝ)*(upper2) + (761974357/100000000000000 : ℝ)*(upper3) + (302506671/100000000000000 : ℝ)*(upper4) + (565697591196997/25000000000000 : ℝ)*(major0) + (565697591196997/25000000000000 : ℝ)*(major1) + (565697591196997/25000000000000 : ℝ)*(major2) + (1511835457066247/50000000000000 : ℝ)*(sp0) + (755928221417247/25000000000000 : ℝ)*(sp1) + (604742438257169/20000000000000 : ℝ)*(sp2) + (750920842352297/50000000000000 : ℝ)*(sp3) + (43649157221/100000000000000 : ℝ)*(sp4) + (24189677761/100000000000000 : ℝ)*(sp7) + (300373174876471/20000000000000 : ℝ)*(f.failure) + (755928640822429/25000000000000 : ℝ)*(f.sum) + (26075307429571/5065000000000000000000000000 : ℝ)*base66 + (533000282838108003/50650000000000000000000000000000 : ℝ)*base67 + (243103049557158003/50650000000000000000000000000000 : ℝ)*base69 + (97498322870708003/50650000000000000000000000000000 : ℝ)*base71 + (1026689379453/2532500000000000000000000000 : ℝ)*base74 + (238963725492591997/50650000000000000000000000000000 : ℝ)*base76 + (84301024563758003/50650000000000000000000000000000 : ℝ)*base77 + (147355825721008003/50650000000000000000000000000000 : ℝ)*base79 + (20581863541489/5065000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2280249/500000000000000000000 : ℝ)*base89 + (2280249/500000000000000000000 : ℝ)*base91 + (2280249/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3237724806239483500651966671/354550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1083645999/50000000000000 : ℝ)*(base19) + (233813143/10000000000000 : ℝ)*(base23) + (239781/10000000000000 : ℝ)*(upper2) + (135738333/50000000000000 : ℝ)*(upper3) + (11718291/6250000000000 : ℝ)*(upper5) + (2293177703236349/100000000000000 : ℝ)*(major0) + (2293177703236349/100000000000000 : ℝ)*(major1) + (2293177703236349/100000000000000 : ℝ)*(major2) + (5413869611/25000000000000 : ℝ)*(sp1) + (25726168649/100000000000000 : ℝ)*(sp2) + (766080113516867/25000000000000 : ℝ)*(sp4) + (122571865251881/4000000000000 : ℝ)*(sp5) + (766073097441847/25000000000000 : ℝ)*(sp6) + (1522034648007647/100000000000000 : ℝ)*(sp7) + (1522034648007647/100000000000000 : ℝ)*(f.failure) + (766080113516867/25000000000000 : ℝ)*(f.sum) + (410421476001583/70910000000000000000000000000 : ℝ)*base65 + (2847179892794651349/202600000000000000000000000000000 : ℝ)*base68 + (2504963156449051349/202600000000000000000000000000000 : ℝ)*base70 + (230462085456651349/202600000000000000000000000000000 : ℝ)*base72 + (250487869028337/70910000000000000000000000000 : ℝ)*base74 + (204708406547851349/202600000000000000000000000000000 : ℝ)*base76 + (180905315237548651/202600000000000000000000000000000 : ℝ)*base77 + (1983789539039851349/202600000000000000000000000000000 : ℝ)*base80 + (221694878773987/70910000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (21341393/2500000000000000000000 : ℝ)*base89 + (21341393/2500000000000000000000 : ℝ)*base91 + (21341393/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1203_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10083/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (187/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9337/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2041/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1203_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1203_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9337/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2041/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1203_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1203_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1203_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9337/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2041/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1203_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
