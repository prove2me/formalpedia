-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1355_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:08:42.838107+00:00
-- url     : https://prove2.me/submissions/f99307b1-0001-41a9-99d1-451b3dc8508f

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
theorem support_rectangle_w1355_s0_0 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1801485931/10000000000 : ℝ)*x 0 + (1497830243/2500000000 : ℝ)*x 1 + (4814001207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1801485931/10000000000 : ℝ)^4315 ≤ (10568642594659/100000000000000 : ℝ)^3291 := by
    have hnat : (1801485931 : ℕ)^4315*100000000000000^3291 ≤ 10568642594659^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801485931 10000000000 10568642594659 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1497830243/2500000000 : ℝ)^4315 ≤ (10217117158419/20000000000000 : ℝ)^3291 := by
    have hnat : (1497830243 : ℕ)^4315*20000000000000^3291 ≤ 10217117158419^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1497830243 2500000000 10217117158419 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4814001207/10000000000 : ℝ)^4315 ≤ (38345771606829/100000000000000 : ℝ)^3291 := by
    have hnat : (4814001207 : ℕ)^4315*100000000000000^3291 ≤ 38345771606829^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814001207 10000000000 38345771606829 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1801485931/10000000000 : ℝ), (1497830243/2500000000 : ℝ), (4814001207/10000000000 : ℝ)] ![(10568642594659/100000000000000 : ℝ), (10217117158419/20000000000000 : ℝ), (38345771606829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1801485931/10000000000 : ℝ)|^4315 ≤ (10568642594659/100000000000000 : ℝ)^3291
        have hw : |(-1801485931/10000000000 : ℝ)|=(1801485931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1497830243/2500000000 : ℝ)|^4315 ≤ (10217117158419/20000000000000 : ℝ)^3291
        have hw : |(1497830243/2500000000 : ℝ)|=(1497830243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4814001207/10000000000 : ℝ)|^4315 ≤ (38345771606829/100000000000000 : ℝ)^3291
        have hw : |(4814001207/10000000000 : ℝ)|=(4814001207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s0_1 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2750178647/5000000000 : ℝ)*x 0 + (-2470039337/10000000000 : ℝ)*x 1 + (4814001677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2750178647/5000000000 : ℝ)^4315 ≤ (45668117355161/100000000000000 : ℝ)^3291 := by
    have hnat : (2750178647 : ℕ)^4315*100000000000000^3291 ≤ 45668117355161^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750178647 5000000000 45668117355161 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2470039337/10000000000 : ℝ)^4315 ≤ (799305305919/5000000000000 : ℝ)^3291 := by
    have hnat : (2470039337 : ℕ)^4315*5000000000000^3291 ≤ 799305305919^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2470039337 10000000000 799305305919 5000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4814001677/10000000000 : ℝ)^4315 ≤ (38345776515479/100000000000000 : ℝ)^3291 := by
    have hnat : (4814001677 : ℕ)^4315*100000000000000^3291 ≤ 38345776515479^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814001677 10000000000 38345776515479 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2750178647/5000000000 : ℝ), (-2470039337/10000000000 : ℝ), (4814001677/10000000000 : ℝ)] ![(45668117355161/100000000000000 : ℝ), (799305305919/5000000000000 : ℝ), (38345776515479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2750178647/5000000000 : ℝ)|^4315 ≤ (45668117355161/100000000000000 : ℝ)^3291
        have hw : |(2750178647/5000000000 : ℝ)|=(2750178647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2470039337/10000000000 : ℝ)|^4315 ≤ (799305305919/5000000000000 : ℝ)^3291
        have hw : |(-2470039337/10000000000 : ℝ)|=(2470039337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4814001677/10000000000 : ℝ)|^4315 ≤ (38345776515479/100000000000000 : ℝ)^3291
        have hw : |(4814001677/10000000000 : ℝ)|=(4814001677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s0_2 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5500357127/10000000000 : ℝ)*x 0 + (4814001257/10000000000 : ℝ)*x 1 + (-2470040067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5500357127/10000000000 : ℝ)^4315 ≤ (45668115537171/100000000000000 : ℝ)^3291 := by
    have hnat : (5500357127 : ℕ)^4315*100000000000000^3291 ≤ 45668115537171^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500357127 10000000000 45668115537171 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4814001257/10000000000 : ℝ)^4315 ≤ (19172886064513/50000000000000 : ℝ)^3291 := by
    have hnat : (4814001257 : ℕ)^4315*50000000000000^3291 ≤ 19172886064513^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814001257 10000000000 19172886064513 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2470040067/10000000000 : ℝ)^4315 ≤ (15986112313/100000000000 : ℝ)^3291 := by
    have hnat : (2470040067 : ℕ)^4315*100000000000^3291 ≤ 15986112313^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2470040067 10000000000 15986112313 100000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5500357127/10000000000 : ℝ), (4814001257/10000000000 : ℝ), (-2470040067/10000000000 : ℝ)] ![(45668115537171/100000000000000 : ℝ), (19172886064513/50000000000000 : ℝ), (15986112313/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5500357127/10000000000 : ℝ)|^4315 ≤ (45668115537171/100000000000000 : ℝ)^3291
        have hw : |(5500357127/10000000000 : ℝ)|=(5500357127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4814001257/10000000000 : ℝ)|^4315 ≤ (19172886064513/50000000000000 : ℝ)^3291
        have hw : |(4814001257/10000000000 : ℝ)|=(4814001257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2470040067/10000000000 : ℝ)|^4315 ≤ (15986112313/100000000000 : ℝ)^3291
        have hw : |(-2470040067/10000000000 : ℝ)|=(2470040067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s0_3 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4176807139/10000000000 : ℝ)*x 0 + (388243241/1250000000 : ℝ)*x 1 + (2791996757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4176807139/10000000000 : ℝ)^4315 ≤ (31832412075769/100000000000000 : ℝ)^3291 := by
    have hnat : (4176807139 : ℕ)^4315*100000000000000^3291 ≤ 31832412075769^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176807139 10000000000 31832412075769 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388243241/1250000000 : ℝ)^4315 ≤ (10793423025979/50000000000000 : ℝ)^3291 := by
    have hnat : (388243241 : ℕ)^4315*50000000000000^3291 ≤ 10793423025979^3291*1250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388243241 1250000000 10793423025979 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2791996757/5000000000 : ℝ)^4315 ≤ (23290370933427/50000000000000 : ℝ)^3291 := by
    have hnat : (2791996757 : ℕ)^4315*50000000000000^3291 ≤ 23290370933427^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791996757 5000000000 23290370933427 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4176807139/10000000000 : ℝ), (388243241/1250000000 : ℝ), (2791996757/5000000000 : ℝ)] ![(31832412075769/100000000000000 : ℝ), (10793423025979/50000000000000 : ℝ), (23290370933427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4176807139/10000000000 : ℝ)|^4315 ≤ (31832412075769/100000000000000 : ℝ)^3291
        have hw : |(4176807139/10000000000 : ℝ)|=(4176807139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(388243241/1250000000 : ℝ)|^4315 ≤ (10793423025979/50000000000000 : ℝ)^3291
        have hw : |(388243241/1250000000 : ℝ)|=(388243241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2791996757/5000000000 : ℝ)|^4315 ≤ (23290370933427/50000000000000 : ℝ)^3291
        have hw : |(2791996757/5000000000 : ℝ)|=(2791996757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s0_4 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1805874807/10000000000 : ℝ)*x 0 + (2422139371/5000000000 : ℝ)*x 1 + (5959961921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1805874807/10000000000 : ℝ)^4315 ≤ (10602414771073/100000000000000 : ℝ)^3291 := by
    have hnat : (1805874807 : ℕ)^4315*100000000000000^3291 ≤ 10602414771073^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805874807 10000000000 10602414771073 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2422139371/5000000000 : ℝ)^4315 ≤ (1933114860773/5000000000000 : ℝ)^3291 := by
    have hnat : (2422139371 : ℕ)^4315*5000000000000^3291 ≤ 1933114860773^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2422139371 5000000000 1933114860773 5000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5959961921/10000000000 : ℝ)^4315 ≤ (50735287995471/100000000000000 : ℝ)^3291 := by
    have hnat : (5959961921 : ℕ)^4315*100000000000000^3291 ≤ 50735287995471^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5959961921 10000000000 50735287995471 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1805874807/10000000000 : ℝ), (2422139371/5000000000 : ℝ), (5959961921/10000000000 : ℝ)] ![(10602414771073/100000000000000 : ℝ), (1933114860773/5000000000000 : ℝ), (50735287995471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1805874807/10000000000 : ℝ)|^4315 ≤ (10602414771073/100000000000000 : ℝ)^3291
        have hw : |(-1805874807/10000000000 : ℝ)|=(1805874807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2422139371/5000000000 : ℝ)|^4315 ≤ (1933114860773/5000000000000 : ℝ)^3291
        have hw : |(2422139371/5000000000 : ℝ)|=(2422139371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5959961921/10000000000 : ℝ)|^4315 ≤ (50735287995471/100000000000000 : ℝ)^3291
        have hw : |(5959961921/10000000000 : ℝ)|=(5959961921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s0_5 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207176739/400000000 : ℝ)*x 0 + (-331020129/2500000000 : ℝ)*x 1 + (2979980723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207176739/400000000 : ℝ)^4315 ≤ (21103236940341/50000000000000 : ℝ)^3291 := by
    have hnat : (207176739 : ℕ)^4315*50000000000000^3291 ≤ 21103236940341^3291*400000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207176739 400000000 21103236940341 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (331020129/2500000000 : ℝ)^4315 ≤ (352912170591/5000000000000 : ℝ)^3291 := by
    have hnat : (331020129 : ℕ)^4315*5000000000000^3291 ≤ 352912170591^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331020129 2500000000 352912170591 5000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2979980723/5000000000 : ℝ)^4315 ≤ (10147056538759/20000000000000 : ℝ)^3291 := by
    have hnat : (2979980723 : ℕ)^4315*20000000000000^3291 ≤ 10147056538759^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2979980723 5000000000 10147056538759 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207176739/400000000 : ℝ), (-331020129/2500000000 : ℝ), (2979980723/5000000000 : ℝ)] ![(21103236940341/50000000000000 : ℝ), (352912170591/5000000000000 : ℝ), (10147056538759/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207176739/400000000 : ℝ)|^4315 ≤ (21103236940341/50000000000000 : ℝ)^3291
        have hw : |(207176739/400000000 : ℝ)|=(207176739/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-331020129/2500000000 : ℝ)|^4315 ≤ (352912170591/5000000000000 : ℝ)^3291
        have hw : |(-331020129/2500000000 : ℝ)|=(331020129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2979980723/5000000000 : ℝ)|^4315 ≤ (10147056538759/20000000000000 : ℝ)^3291
        have hw : |(2979980723/5000000000 : ℝ)|=(2979980723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s0_6 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5179418361/10000000000 : ℝ)*x 0 + (2979981013/5000000000 : ℝ)*x 1 + (-1324079763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5179418361/10000000000 : ℝ)^4315 ≤ (21103236331329/50000000000000 : ℝ)^3291 := by
    have hnat : (5179418361 : ℕ)^4315*50000000000000^3291 ≤ 21103236331329^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179418361 10000000000 21103236331329 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2979981013/5000000000 : ℝ)^4315 ≤ (2536764458371/5000000000000 : ℝ)^3291 := by
    have hnat : (2979981013 : ℕ)^4315*5000000000000^3291 ≤ 2536764458371^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2979981013 5000000000 2536764458371 5000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1324079763/10000000000 : ℝ)^4315 ≤ (352911907443/5000000000000 : ℝ)^3291 := by
    have hnat : (1324079763 : ℕ)^4315*5000000000000^3291 ≤ 352911907443^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324079763 10000000000 352911907443 5000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5179418361/10000000000 : ℝ), (2979981013/5000000000 : ℝ), (-1324079763/10000000000 : ℝ)] ![(21103236331329/50000000000000 : ℝ), (2536764458371/5000000000000 : ℝ), (352911907443/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5179418361/10000000000 : ℝ)|^4315 ≤ (21103236331329/50000000000000 : ℝ)^3291
        have hw : |(5179418361/10000000000 : ℝ)|=(5179418361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2979981013/5000000000 : ℝ)|^4315 ≤ (2536764458371/5000000000000 : ℝ)^3291
        have hw : |(2979981013/5000000000 : ℝ)|=(2979981013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1324079763/10000000000 : ℝ)|^4315 ≤ (352911907443/5000000000000 : ℝ)^3291
        have hw : |(-1324079763/10000000000 : ℝ)|=(1324079763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s0_7 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4186041677/10000000000 : ℝ)*x 0 + (345016627/625000000 : ℝ)*x 1 + (396493861/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186041677/10000000000 : ℝ)^4315 ≤ (31924720746357/100000000000000 : ℝ)^3291 := by
    have hnat : (4186041677 : ℕ)^4315*100000000000000^3291 ≤ 31924720746357^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186041677 10000000000 31924720746357 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345016627/625000000 : ℝ)^4315 ≤ (45884969209813/100000000000000 : ℝ)^3291 := by
    have hnat : (345016627 : ℕ)^4315*100000000000000^3291 ≤ 45884969209813^3291*625000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345016627 625000000 45884969209813 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396493861/1250000000 : ℝ)^4315 ≤ (22190310033437/100000000000000 : ℝ)^3291 := by
    have hnat : (396493861 : ℕ)^4315*100000000000000^3291 ≤ 22190310033437^3291*1250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396493861 1250000000 22190310033437 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186041677/10000000000 : ℝ), (345016627/625000000 : ℝ), (396493861/1250000000 : ℝ)] ![(31924720746357/100000000000000 : ℝ), (45884969209813/100000000000000 : ℝ), (22190310033437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186041677/10000000000 : ℝ)|^4315 ≤ (31924720746357/100000000000000 : ℝ)^3291
        have hw : |(4186041677/10000000000 : ℝ)|=(4186041677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(345016627/625000000 : ℝ)|^4315 ≤ (45884969209813/100000000000000 : ℝ)^3291
        have hw : |(345016627/625000000 : ℝ)|=(345016627/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(396493861/1250000000 : ℝ)|^4315 ≤ (22190310033437/100000000000000 : ℝ)^3291
        have hw : |(396493861/1250000000 : ℝ)|=(396493861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1355_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1511/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13389/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2157/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2157 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2157*1^512 ≤ 0^512*1^2157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2157 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2157/512 : ℝ) ≤ (16455546061131587/781250000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2157 ≤ (16455546061131587/781250000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2157*781250000000000000^512 ≤ 16455546061131587^512*5^2157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 16455546061131587 781250000000000000 2157 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (16455546061131587/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2157 := by
      have hnat : (1 : ℕ)^512*1^2157 ≤ 1^2157*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (797705546061131587/781250000000000000 : ℝ) ≤ (10049600124303977/10000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (797705546061131587/781250000000000000 : ℝ)^512 ≤ (10049600124303977/10000000000000000 : ℝ)^2157 := by
      have hnat : (797705546061131587 : ℕ)^512*10000000000000000^2157 ≤ 10049600124303977^2157*781250000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        797705546061131587 781250000000000000 10049600124303977 10000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10049600124303977/10000000000000000 : ℝ)) (X := (797705546061131587/781250000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (407080546061131587/390625000000000000 : ℝ) ≤ (5049600124303977/5000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (407080546061131587/390625000000000000 : ℝ)^512 ≤ (5049600124303977/5000000000000000 : ℝ)^2157 := by
      have hnat : (407080546061131587 : ℕ)^512*5000000000000000^2157 ≤ 5049600124303977^2157*390625000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        407080546061131587 390625000000000000 5049600124303977 5000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5049600124303977/5000000000000000 : ℝ)) (X := (407080546061131587/390625000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(49600124303977/4000000000000000 : ℝ)*(0 : ℝ))^(2157/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(49600124303977/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16455546061131587/781250000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(49600124303977/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2157/512 : ℝ) := by
    rw [show (1 : ℝ)+(49600124303977/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10049600124303977/10000000000000000 : ℝ) by norm_num, show 1+(16455546061131587/781250000000000000 : ℝ)+(0 : ℝ)=(797705546061131587/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16455546061131587/781250000000000000 : ℝ) ≤ ((1 : ℝ)+2*(49600124303977/4000000000000000 : ℝ)*(2/5 : ℝ))^(2157/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(49600124303977/4000000000000000 : ℝ)*(2/5 : ℝ)=(5049600124303977/5000000000000000 : ℝ) by norm_num, show 1+2*(16455546061131587/781250000000000000 : ℝ)=(407080546061131587/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(49600124303977/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49600124303977/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(49600124303977/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49600124303977/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(49600124303977/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49600124303977/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1801485931/10000000000 : ℝ)*X 0 0+(1497830243/2500000000 : ℝ)*X 0 1+(4814001207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2750178647/5000000000 : ℝ)*X 1 0+(-2470039337/10000000000 : ℝ)*X 1 1+(4814001677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5500357127/10000000000 : ℝ)*X 2 0+(4814001257/10000000000 : ℝ)*X 2 1+(-2470040067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4176807139/10000000000 : ℝ)*X 0 0+(388243241/1250000000 : ℝ)*X 0 1+(2791996757/5000000000 : ℝ)*X 0 2+(4176807139/10000000000 : ℝ)*X 1 0+(388243241/1250000000 : ℝ)*X 1 1+(2791996757/5000000000 : ℝ)*X 1 2+(4176807139/10000000000 : ℝ)*X 2 0+(388243241/1250000000 : ℝ)*X 2 1+(2791996757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1805874807/10000000000 : ℝ)*X 0 0+(2422139371/5000000000 : ℝ)*X 0 1+(5959961921/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((207176739/400000000 : ℝ)*X 1 0+(-331020129/2500000000 : ℝ)*X 1 1+(2979980723/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5179418361/10000000000 : ℝ)*X 2 0+(2979981013/5000000000 : ℝ)*X 2 1+(-1324079763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4186041677/10000000000 : ℝ)*X 0 0+(345016627/625000000 : ℝ)*X 0 1+(396493861/1250000000 : ℝ)*X 0 2+(4186041677/10000000000 : ℝ)*X 1 0+(345016627/625000000 : ℝ)*X 1 1+(396493861/1250000000 : ℝ)*X 1 2+(4186041677/10000000000 : ℝ)*X 2 0+(345016627/625000000 : ℝ)*X 2 1+(396493861/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (721995700247791825639197/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2469443/1562500000000 : ℝ)*(base1) + (421795419/25000000000000 : ℝ)*(base19) + (1661392603/100000000000000 : ℝ)*(base23) + (276297063/100000000000000 : ℝ)*(upper3) + (80589163/100000000000000 : ℝ)*(upper5) + (313236585765287/50000000000000 : ℝ)*(major0) + (313236585765287/50000000000000 : ℝ)*(major1) + (313236585765287/50000000000000 : ℝ)*(major2) + (849392809701193/100000000000000 : ℝ)*(sp0) + (424697936572099/50000000000000 : ℝ)*(sp1) + (849395898933271/100000000000000 : ℝ)*(sp2) + (201772806685033/50000000000000 : ℝ)*(sp3) + (613583629/12500000000000 : ℝ)*(sp4) + (1385327809/50000000000000 : ℝ)*(sp7) + (100887135517509/25000000000000 : ℝ)*(f.failure) + (849397560325873/100000000000000 : ℝ)*(f.sum) + (109066757346399/100000000000000000000000000000 : ℝ)*base65 + (153567489846399/200000000000000000000000000000 : ℝ)*base67 + (1213535463553601/200000000000000000000000000000 : ℝ)*base70 + (1064867791753601/200000000000000000000000000000 : ℝ)*base72 + (354542532846399/100000000000000000000000000000 : ℝ)*base73 + (1315845388153601/200000000000000000000000000000 : ℝ)*base76 + (1196706232753601/200000000000000000000000000000 : ℝ)*base78 + (975929371553601/200000000000000000000000000000 : ℝ)*base80 + (27640392453601/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1657423/1250000000000000000000 : ℝ)*base89 + (1657423/1250000000000000000000 : ℝ)*base91 + (1657423/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (286644617150314912802991/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (308097049/25000000000000 : ℝ)*(base19) + (1441540061/100000000000000 : ℝ)*(base23) + (43879261/20000000000000 : ℝ)*(base39) + (65506731/50000000000000 : ℝ)*(upper3) + (22560681/10000000000000 : ℝ)*(upper5) + (165268494400199/25000000000000 : ℝ)*(major0) + (165268494400199/25000000000000 : ℝ)*(major1) + (661073758204491/100000000000000 : ℝ)*(major2) + (2829954243/100000000000000 : ℝ)*(sp1) + (766942569/25000000000000 : ℝ)*(sp2) + (224077630652093/25000000000000 : ℝ)*(sp4) + (896306460265933/100000000000000 : ℝ)*(sp5) + (896306232694339/100000000000000 : ℝ)*(sp6) + (106459243581599/25000000000000 : ℝ)*(sp7) + (106459243581599/25000000000000 : ℝ)*(f.failure) + (224077685501169/25000000000000 : ℝ)*(f.sum) + (83293716526399/400000000000000000000000000000 : ℝ)*base65 + (472511132160707/400000000000000000000000000000 : ℝ)*base67 + (1173837260708577/100000000000000000000000000000 : ℝ)*base70 + (659972073039293/400000000000000000000000000000 : ℝ)*base72 + (882997530526399/400000000000000000000000000000 : ℝ)*base73 + (824505462408577/100000000000000000000000000000 : ℝ)*base76 + (219845187008577/100000000000000000000000000000 : ℝ)*base78 + (309528123491423/100000000000000000000000000000 : ℝ)*base79 + (187244509658577/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (3514653/1250000000000000000000 : ℝ)*base89 + (3514653/1250000000000000000000 : ℝ)*base91 + (3514653/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1355_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1511/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13389/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1355_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1355_s1_0 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-124026641/625000000 : ℝ)*x 0 + (1127271111/2000000000 : ℝ)*x 1 + (5051796037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (124026641/625000000 : ℝ)^4315 ≤ (11997560316821/100000000000000 : ℝ)^3291 := by
    have hnat : (124026641 : ℕ)^4315*100000000000000^3291 ≤ 11997560316821^3291*625000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124026641 625000000 11997560316821 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127271111/2000000000 : ℝ)^4315 ≤ (23577140289317/50000000000000 : ℝ)^3291 := by
    have hnat : (1127271111 : ℕ)^4315*50000000000000^3291 ≤ 23577140289317^3291*2000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127271111 2000000000 23577140289317 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5051796037/10000000000 : ℝ)^4315 ≤ (40848159091073/100000000000000 : ℝ)^3291 := by
    have hnat : (5051796037 : ℕ)^4315*100000000000000^3291 ≤ 40848159091073^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5051796037 10000000000 40848159091073 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-124026641/625000000 : ℝ), (1127271111/2000000000 : ℝ), (5051796037/10000000000 : ℝ)] ![(11997560316821/100000000000000 : ℝ), (23577140289317/50000000000000 : ℝ), (40848159091073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-124026641/625000000 : ℝ)|^4315 ≤ (11997560316821/100000000000000 : ℝ)^3291
        have hw : |(-124026641/625000000 : ℝ)|=(124026641/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127271111/2000000000 : ℝ)|^4315 ≤ (23577140289317/50000000000000 : ℝ)^3291
        have hw : |(1127271111/2000000000 : ℝ)|=(1127271111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5051796037/10000000000 : ℝ)|^4315 ≤ (40848159091073/100000000000000 : ℝ)^3291
        have hw : |(5051796037/10000000000 : ℝ)|=(5051796037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s1_1 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404365871/10000000000 : ℝ)*x 0 + (-2296017001/10000000000 : ℝ)*x 1 + (5051796693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404365871/10000000000 : ℝ)^4315 ≤ (44625987037161/100000000000000 : ℝ)^3291 := by
    have hnat : (5404365871 : ℕ)^4315*100000000000000^3291 ≤ 44625987037161^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404365871 10000000000 44625987037161 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2296017001/10000000000 : ℝ)^4315 ≤ (581033876563/4000000000000 : ℝ)^3291 := by
    have hnat : (2296017001 : ℕ)^4315*4000000000000^3291 ≤ 581033876563^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296017001 10000000000 581033876563 4000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5051796693/10000000000 : ℝ)^4315 ≤ (40848166045853/100000000000000 : ℝ)^3291 := by
    have hnat : (5051796693 : ℕ)^4315*100000000000000^3291 ≤ 40848166045853^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5051796693 10000000000 40848166045853 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404365871/10000000000 : ℝ), (-2296017001/10000000000 : ℝ), (5051796693/10000000000 : ℝ)] ![(44625987037161/100000000000000 : ℝ), (581033876563/4000000000000 : ℝ), (40848166045853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404365871/10000000000 : ℝ)|^4315 ≤ (44625987037161/100000000000000 : ℝ)^3291
        have hw : |(5404365871/10000000000 : ℝ)|=(5404365871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2296017001/10000000000 : ℝ)|^4315 ≤ (581033876563/4000000000000 : ℝ)^3291
        have hw : |(-2296017001/10000000000 : ℝ)|=(2296017001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5051796693/10000000000 : ℝ)|^4315 ≤ (40848166045853/100000000000000 : ℝ)^3291
        have hw : |(5051796693/10000000000 : ℝ)|=(5051796693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s1_2 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540436591/1000000000 : ℝ)*x 0 + (5051796163/10000000000 : ℝ)*x 1 + (-1148008813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540436591/1000000000 : ℝ)^4315 ≤ (22312993729701/50000000000000 : ℝ)^3291 := by
    have hnat : (540436591 : ℕ)^4315*50000000000000^3291 ≤ 22312993729701^3291*1000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540436591 1000000000 22312993729701 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5051796163/10000000000 : ℝ)^4315 ≤ (40848160426899/100000000000000 : ℝ)^3291 := by
    have hnat : (5051796163 : ℕ)^4315*100000000000000^3291 ≤ 40848160426899^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5051796163 10000000000 40848160426899 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1148008813/5000000000 : ℝ)^4315 ≤ (2905170419697/20000000000000 : ℝ)^3291 := by
    have hnat : (1148008813 : ℕ)^4315*20000000000000^3291 ≤ 2905170419697^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148008813 5000000000 2905170419697 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540436591/1000000000 : ℝ), (5051796163/10000000000 : ℝ), (-1148008813/5000000000 : ℝ)] ![(22312993729701/50000000000000 : ℝ), (40848160426899/100000000000000 : ℝ), (2905170419697/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540436591/1000000000 : ℝ)|^4315 ≤ (22312993729701/50000000000000 : ℝ)^3291
        have hw : |(540436591/1000000000 : ℝ)|=(540436591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5051796163/10000000000 : ℝ)|^4315 ≤ (40848160426899/100000000000000 : ℝ)^3291
        have hw : |(5051796163/10000000000 : ℝ)|=(5051796163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1148008813/5000000000 : ℝ)|^4315 ≤ (2905170419697/20000000000000 : ℝ)^3291
        have hw : |(-1148008813/5000000000 : ℝ)|=(1148008813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s1_3 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2144993037/5000000000 : ℝ)*x 0 + (1857719697/5000000000 : ℝ)*x 1 + (618228719/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144993037/5000000000 : ℝ)^4315 ≤ (32968101052961/100000000000000 : ℝ)^3291 := by
    have hnat : (2144993037 : ℕ)^4315*100000000000000^3291 ≤ 32968101052961^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144993037 5000000000 32968101052961 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1857719697/5000000000 : ℝ)^4315 ≤ (27303489201233/100000000000000 : ℝ)^3291 := by
    have hnat : (1857719697 : ℕ)^4315*100000000000000^3291 ≤ 27303489201233^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1857719697 5000000000 27303489201233 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (618228719/1250000000 : ℝ)^4315 ≤ (39728409727181/100000000000000 : ℝ)^3291 := by
    have hnat : (618228719 : ℕ)^4315*100000000000000^3291 ≤ 39728409727181^3291*1250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618228719 1250000000 39728409727181 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2144993037/5000000000 : ℝ), (1857719697/5000000000 : ℝ), (618228719/1250000000 : ℝ)] ![(32968101052961/100000000000000 : ℝ), (27303489201233/100000000000000 : ℝ), (39728409727181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2144993037/5000000000 : ℝ)|^4315 ≤ (32968101052961/100000000000000 : ℝ)^3291
        have hw : |(2144993037/5000000000 : ℝ)|=(2144993037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1857719697/5000000000 : ℝ)|^4315 ≤ (27303489201233/100000000000000 : ℝ)^3291
        have hw : |(1857719697/5000000000 : ℝ)|=(1857719697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(618228719/1250000000 : ℝ)|^4315 ≤ (39728409727181/100000000000000 : ℝ)^3291
        have hw : |(618228719/1250000000 : ℝ)|=(618228719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s1_4 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1984939557/10000000000 : ℝ)*x 0 + (5059058221/10000000000 : ℝ)*x 1 + (703620323/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1984939557/10000000000 : ℝ)^4315 ≤ (6000814718333/50000000000000 : ℝ)^3291 := by
    have hnat : (1984939557 : ℕ)^4315*50000000000000^3291 ≤ 6000814718333^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984939557 10000000000 6000814718333 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5059058221/10000000000 : ℝ)^4315 ≤ (20462584262671/50000000000000 : ℝ)^3291 := by
    have hnat : (5059058221 : ℕ)^4315*50000000000000^3291 ≤ 20462584262671^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5059058221 10000000000 20462584262671 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (703620323/1250000000 : ℝ)^4315 ≤ (23536601011521/50000000000000 : ℝ)^3291 := by
    have hnat : (703620323 : ℕ)^4315*50000000000000^3291 ≤ 23536601011521^3291*1250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      703620323 1250000000 23536601011521 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1984939557/10000000000 : ℝ), (5059058221/10000000000 : ℝ), (703620323/1250000000 : ℝ)] ![(6000814718333/50000000000000 : ℝ), (20462584262671/50000000000000 : ℝ), (23536601011521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1984939557/10000000000 : ℝ)|^4315 ≤ (6000814718333/50000000000000 : ℝ)^3291
        have hw : |(-1984939557/10000000000 : ℝ)|=(1984939557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5059058221/10000000000 : ℝ)|^4315 ≤ (20462584262671/50000000000000 : ℝ)^3291
        have hw : |(5059058221/10000000000 : ℝ)|=(5059058221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(703620323/1250000000 : ℝ)|^4315 ≤ (23536601011521/50000000000000 : ℝ)^3291
        have hw : |(703620323/1250000000 : ℝ)|=(703620323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s1_5 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050503451/2000000000 : ℝ)*x 0 + (-429712729/2500000000 : ℝ)*x 1 + (5628962641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050503451/2000000000 : ℝ)^4315 ≤ (8597840272233/20000000000000 : ℝ)^3291 := by
    have hnat : (1050503451 : ℕ)^4315*20000000000000^3291 ≤ 8597840272233^3291*2000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050503451 2000000000 8597840272233 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429712729/2500000000 : ℝ)^4315 ≤ (198751919367/2000000000000 : ℝ)^3291 := by
    have hnat : (429712729 : ℕ)^4315*2000000000000^3291 ≤ 198751919367^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429712729 2500000000 198751919367 2000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5628962641/10000000000 : ℝ)^4315 ≤ (1471037582751/3125000000000 : ℝ)^3291 := by
    have hnat : (5628962641 : ℕ)^4315*3125000000000^3291 ≤ 1471037582751^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5628962641 10000000000 1471037582751 3125000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050503451/2000000000 : ℝ), (-429712729/2500000000 : ℝ), (5628962641/10000000000 : ℝ)] ![(8597840272233/20000000000000 : ℝ), (198751919367/2000000000000 : ℝ), (1471037582751/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050503451/2000000000 : ℝ)|^4315 ≤ (8597840272233/20000000000000 : ℝ)^3291
        have hw : |(1050503451/2000000000 : ℝ)|=(1050503451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429712729/2500000000 : ℝ)|^4315 ≤ (198751919367/2000000000000 : ℝ)^3291
        have hw : |(-429712729/2500000000 : ℝ)|=(429712729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5628962641/10000000000 : ℝ)|^4315 ≤ (1471037582751/3125000000000 : ℝ)^3291
        have hw : |(5628962641/10000000000 : ℝ)|=(5628962641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s1_6 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105050343/200000000 : ℝ)*x 0 + (35181017/62500000 : ℝ)*x 1 + (-1718850951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105050343/200000000 : ℝ)^4315 ≤ (21494600117199/50000000000000 : ℝ)^3291 := by
    have hnat : (105050343 : ℕ)^4315*50000000000000^3291 ≤ 21494600117199^3291*200000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105050343 200000000 21494600117199 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35181017/62500000 : ℝ)^4315 ≤ (47073203514247/100000000000000 : ℝ)^3291 := by
    have hnat : (35181017 : ℕ)^4315*100000000000000^3291 ≤ 47073203514247^3291*62500000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35181017 62500000 47073203514247 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1718850951/10000000000 : ℝ)^4315 ≤ (4968798116833/50000000000000 : ℝ)^3291 := by
    have hnat : (1718850951 : ℕ)^4315*50000000000000^3291 ≤ 4968798116833^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1718850951 10000000000 4968798116833 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105050343/200000000 : ℝ), (35181017/62500000 : ℝ), (-1718850951/10000000000 : ℝ)] ![(21494600117199/50000000000000 : ℝ), (47073203514247/100000000000000 : ℝ), (4968798116833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105050343/200000000 : ℝ)|^4315 ≤ (21494600117199/50000000000000 : ℝ)^3291
        have hw : |(105050343/200000000 : ℝ)|=(105050343/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35181017/62500000 : ℝ)|^4315 ≤ (47073203514247/100000000000000 : ℝ)^3291
        have hw : |(35181017/62500000 : ℝ)|=(35181017/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1718850951/10000000000 : ℝ)|^4315 ≤ (4968798116833/50000000000000 : ℝ)^3291
        have hw : |(-1718850951/10000000000 : ℝ)|=(1718850951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s1_7 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2145533503/5000000000 : ℝ)*x 0 + (493054531/1000000000 : ℝ)*x 1 + (1865498997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145533503/5000000000 : ℝ)^4315 ≤ (32978993021167/100000000000000 : ℝ)^3291 := by
    have hnat : (2145533503 : ℕ)^4315*100000000000000^3291 ≤ 32978993021167^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145533503 5000000000 32978993021167 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (493054531/1000000000 : ℝ)^4315 ≤ (4945938740041/12500000000000 : ℝ)^3291 := by
    have hnat : (493054531 : ℕ)^4315*12500000000000^3291 ≤ 4945938740041^3291*1000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493054531 1000000000 4945938740041 12500000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1865498997/5000000000 : ℝ)^4315 ≤ (27453497046831/100000000000000 : ℝ)^3291 := by
    have hnat : (1865498997 : ℕ)^4315*100000000000000^3291 ≤ 27453497046831^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865498997 5000000000 27453497046831 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2145533503/5000000000 : ℝ), (493054531/1000000000 : ℝ), (1865498997/5000000000 : ℝ)] ![(32978993021167/100000000000000 : ℝ), (4945938740041/12500000000000 : ℝ), (27453497046831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2145533503/5000000000 : ℝ)|^4315 ≤ (32978993021167/100000000000000 : ℝ)^3291
        have hw : |(2145533503/5000000000 : ℝ)|=(2145533503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(493054531/1000000000 : ℝ)|^4315 ≤ (4945938740041/12500000000000 : ℝ)^3291
        have hw : |(493054531/1000000000 : ℝ)|=(493054531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1865498997/5000000000 : ℝ)|^4315 ≤ (27453497046831/100000000000000 : ℝ)^3291
        have hw : |(1865498997/5000000000 : ℝ)|=(1865498997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1355_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13389/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1511/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (701/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3873/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13389/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1511/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13389/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1511/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13389/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1511/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13389/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1511/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13389/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1511/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13389/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1511/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1511/100000 : ℝ) ^ (2157/512 : ℝ) ≤ (1067604352151/50000000000000000000 : ℝ) := by
    have hpowers : (1511/100000 : ℝ)^2157 ≤ (1067604352151/50000000000000000000 : ℝ)^512 := by
      have hnat : (1511 : ℕ)^2157*50000000000000000000^512 ≤ 1067604352151^512*100000^2157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1511 100000 1067604352151 50000000000000000000 2157 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1511/100000 : ℝ)) (X := (1067604352151/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hpowhi : (13389/50000 : ℝ) ^ (2157/512 : ℝ) ≤ (12137853756590277/3125000000000000000 : ℝ) := by
    have hpowers : (13389/50000 : ℝ)^2157 ≤ (12137853756590277/3125000000000000000 : ℝ)^512 := by
      have hnat : (13389 : ℕ)^2157*3125000000000000000^512 ≤ 12137853756590277^512*50000^2157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13389 50000 12137853756590277 3125000000000000000 2157 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13389/50000 : ℝ)) (X := (12137853756590277/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000001067604352151/25000000000000000000 : ℝ) ≤ (10000000101365493/10000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (25000001067604352151/25000000000000000000 : ℝ)^512 ≤ (10000000101365493/10000000000000000 : ℝ)^2157 := by
      have hnat : (25000001067604352151 : ℕ)^512*10000000000000000^2157 ≤ 10000000101365493^2157*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000001067604352151 25000000000000000000 10000000101365493 10000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000101365493/10000000000000000 : ℝ)) (X := (25000001067604352151/25000000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50194206727709796583/50000000000000000000 : ℝ) ≤ (10009206018524137/10000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (50194206727709796583/50000000000000000000 : ℝ)^512 ≤ (10009206018524137/10000000000000000 : ℝ)^2157 := by
      have hnat : (50194206727709796583 : ℕ)^512*10000000000000000^2157 ≤ 10009206018524137^2157*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50194206727709796583 50000000000000000000 10009206018524137 10000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009206018524137/10000000000000000 : ℝ)) (X := (50194206727709796583/50000000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1574637853756590277/1562500000000000000 : ℝ) ≤ (10018411935682781/10000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (1574637853756590277/1562500000000000000 : ℝ)^512 ≤ (10018411935682781/10000000000000000 : ℝ)^2157 := by
      have hnat : (1574637853756590277 : ℕ)^512*10000000000000000^2157 ≤ 10018411935682781^2157*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1574637853756590277 1562500000000000000 10018411935682781 10000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10018411935682781/10000000000000000 : ℝ)) (X := (1574637853756590277/1562500000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1067604352151/50000000000000000000 : ℝ) ≤ ((252642182279548489463/252670000000000000000 : ℝ)+2*(2301479289661/631675000000000 : ℝ)*(1511/100000 : ℝ))^(2157/512 : ℝ) := by
    rw [show (252642182279548489463/252670000000000000000 : ℝ)+2*(2301479289661/631675000000000 : ℝ)*(1511/100000 : ℝ)=(10000000101365493/10000000000000000 : ℝ) by norm_num, show 1+2*(1067604352151/50000000000000000000 : ℝ)=(25000001067604352151/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12137853756590277/3125000000000000000 : ℝ)+(1067604352151/50000000000000000000 : ℝ) ≤ ((252642182279548489463/252670000000000000000 : ℝ)+(2301479289661/631675000000000 : ℝ)*((13389/50000 : ℝ)+(1511/100000 : ℝ)))^(2157/512 : ℝ) := by
    rw [show (252642182279548489463/252670000000000000000 : ℝ)+(2301479289661/631675000000000 : ℝ)*((13389/50000 : ℝ)+(1511/100000 : ℝ))=(10009206018524137/10000000000000000 : ℝ) by norm_num, show 1+(12137853756590277/3125000000000000000 : ℝ)+(1067604352151/50000000000000000000 : ℝ)=(50194206727709796583/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12137853756590277/3125000000000000000 : ℝ) ≤ ((252642182279548489463/252670000000000000000 : ℝ)+2*(2301479289661/631675000000000 : ℝ)*(13389/50000 : ℝ))^(2157/512 : ℝ) := by
    rw [show (252642182279548489463/252670000000000000000 : ℝ)+2*(2301479289661/631675000000000 : ℝ)*(13389/50000 : ℝ)=(10018411935682781/10000000000000000 : ℝ) by norm_num, show 1+2*(12137853756590277/3125000000000000000 : ℝ)=(1574637853756590277/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (252642182279548489463/252670000000000000000 : ℝ)*(X 1 0+X 2 0)+(2301479289661/631675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (1511/100000 : ℝ)) (hi := (13389/50000 : ℝ)) (c := (252642182279548489463/252670000000000000000 : ℝ)) (alpha := (2301479289661/631675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (252642182279548489463/252670000000000000000 : ℝ)*(X 0 1+X 2 1)+(2301479289661/631675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (1511/100000 : ℝ)) (hi := (13389/50000 : ℝ)) (c := (252642182279548489463/252670000000000000000 : ℝ)) (alpha := (2301479289661/631675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (252642182279548489463/252670000000000000000 : ℝ)*(X 0 2+X 1 2)+(2301479289661/631675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (1511/100000 : ℝ)) (hi := (13389/50000 : ℝ)) (c := (252642182279548489463/252670000000000000000 : ℝ)) (alpha := (2301479289661/631675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-124026641/625000000 : ℝ)*X 0 0+(1127271111/2000000000 : ℝ)*X 0 1+(5051796037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5404365871/10000000000 : ℝ)*X 1 0+(-2296017001/10000000000 : ℝ)*X 1 1+(5051796693/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((540436591/1000000000 : ℝ)*X 2 0+(5051796163/10000000000 : ℝ)*X 2 1+(-1148008813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2144993037/5000000000 : ℝ)*X 0 0+(1857719697/5000000000 : ℝ)*X 0 1+(618228719/1250000000 : ℝ)*X 0 2+(2144993037/5000000000 : ℝ)*X 1 0+(1857719697/5000000000 : ℝ)*X 1 1+(618228719/1250000000 : ℝ)*X 1 2+(2144993037/5000000000 : ℝ)*X 2 0+(1857719697/5000000000 : ℝ)*X 2 1+(618228719/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1984939557/10000000000 : ℝ)*X 0 0+(5059058221/10000000000 : ℝ)*X 0 1+(703620323/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050503451/2000000000 : ℝ)*X 1 0+(-429712729/2500000000 : ℝ)*X 1 1+(5628962641/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((105050343/200000000 : ℝ)*X 2 0+(35181017/62500000 : ℝ)*X 2 1+(-1718850951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2145533503/5000000000 : ℝ)*X 0 0+(493054531/1000000000 : ℝ)*X 0 1+(1865498997/5000000000 : ℝ)*X 0 2+(2145533503/5000000000 : ℝ)*X 1 0+(493054531/1000000000 : ℝ)*X 1 1+(1865498997/5000000000 : ℝ)*X 1 2+(2145533503/5000000000 : ℝ)*X 2 0+(493054531/1000000000 : ℝ)*X 2 1+(1865498997/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15902240049367578143619010467/6316750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (470133/800000000000 : ℝ)*(base16) + (96031867/100000000000000 : ℝ)*(base19) + (20095379/10000000000000 : ℝ)*(base23) + (4976349/20000000000000 : ℝ)*(upper2) + (207233/5000000000000 : ℝ)*(upper3) + (630861197247703/50000000000000 : ℝ)*(major0) + (630861197247703/50000000000000 : ℝ)*(major1) + (630861197247703/50000000000000 : ℝ)*(major2) + (1710692263992431/100000000000000 : ℝ)*(sp0) + (171069429067367/10000000000000 : ℝ)*(sp1) + (1710693809253669/100000000000000 : ℝ)*(sp2) + (203187564900729/25000000000000 : ℝ)*(sp3) + (545369933/25000000000000 : ℝ)*(sp4) + (6801011/1562500000000 : ℝ)*(sp6) + (203187564900729/25000000000000 : ℝ)*(f.failure) + (1710694445472163/100000000000000 : ℝ)*(f.sum) + (115449889554269/31583750000000000000000000000 : ℝ)*base66 + (17517051229443846511/12633500000000000000000000000000000 : ℝ)*base68 + (79496324896974846511/12633500000000000000000000000000000 : ℝ)*base70 + (11164352264089346511/12633500000000000000000000000000000 : ℝ)*base72 + (277204368193963/63167500000000000000000000000 : ℝ)*base74 + (85471540677212653489/12633500000000000000000000000000000 : ℝ)*base75 + (113361544853559346511/12633500000000000000000000000000000 : ℝ)*base78 + (57886929031231153489/12633500000000000000000000000000000 : ℝ)*base79 + (307641268014213/63167500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (10678763/1250000000000000000000 : ℝ)*base89 + (10678763/1250000000000000000000 : ℝ)*base91 + (10678763/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10149659607686210038671132477/1263350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216781/250000000000 : ℝ)*(base1) + (1636362657/100000000000000 : ℝ)*(base19) + (799639577/50000000000000 : ℝ)*(base23) + (11675419/6250000000000 : ℝ)*(upper3) + (35490263/20000000000000 : ℝ)*(upper5) + (129416413500793/10000000000000 : ℝ)*(major0) + (129416413500793/10000000000000 : ℝ)*(major1) + (129416413500793/10000000000000 : ℝ)*(major2) + (8483610643/100000000000000 : ℝ)*(sp1) + (8414188153/100000000000000 : ℝ)*(sp2) + (350936035861413/20000000000000 : ℝ)*(sp4) + (438667493155341/25000000000000 : ℝ)*(sp5) + (877335039563679/50000000000000 : ℝ)*(sp6) + (833647822911279/100000000000000 : ℝ)*(sp7) + (833647909623679/100000000000000 : ℝ)*(f.failure) + (350936018518933/20000000000000 : ℝ)*(f.sum) + (41877177729161/25267000000000000000000000000 : ℝ)*base65 + (3329288916356655841/2526700000000000000000000000000000 : ℝ)*base68 + (6598453220264355841/2526700000000000000000000000000000 : ℝ)*base70 + (2898069742566944159/2526700000000000000000000000000000 : ℝ)*base71 + (27213475441443/25267000000000000000000000000 : ℝ)*base73 + (13944603286223544159/2526700000000000000000000000000000 : ℝ)*base75 + (10885212816554955841/2526700000000000000000000000000000 : ℝ)*base78 + (11232602697574455841/2526700000000000000000000000000000 : ℝ)*base80 + (15168985294323/12633500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (28132413/5000000000000000000000 : ℝ)*base89 + (28132413/5000000000000000000000 : ℝ)*base91 + (28132413/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1355_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13389/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1511/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (701/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3873/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1355_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1355_s2_0 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2023460331/10000000000 : ℝ)*x 0 + (5476245239/10000000000 : ℝ)*x 1 + (5186884679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2023460331/10000000000 : ℝ)^4315 ≤ (12307927542673/100000000000000 : ℝ)^3291 := by
    have hnat : (2023460331 : ℕ)^4315*100000000000000^3291 ≤ 12307927542673^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023460331 10000000000 12307927542673 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5476245239/10000000000 : ℝ)^4315 ≤ (5675726076931/12500000000000 : ℝ)^3291 := by
    have hnat : (5476245239 : ℕ)^4315*12500000000000^3291 ≤ 5675726076931^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476245239 10000000000 5675726076931 12500000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5186884679/10000000000 : ℝ)^4315 ≤ (42286263830649/100000000000000 : ℝ)^3291 := by
    have hnat : (5186884679 : ℕ)^4315*100000000000000^3291 ≤ 42286263830649^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186884679 10000000000 42286263830649 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2023460331/10000000000 : ℝ), (5476245239/10000000000 : ℝ), (5186884679/10000000000 : ℝ)] ![(12307927542673/100000000000000 : ℝ), (5675726076931/12500000000000 : ℝ), (42286263830649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2023460331/10000000000 : ℝ)|^4315 ≤ (12307927542673/100000000000000 : ℝ)^3291
        have hw : |(-2023460331/10000000000 : ℝ)|=(2023460331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5476245239/10000000000 : ℝ)|^4315 ≤ (5675726076931/12500000000000 : ℝ)^3291
        have hw : |(5476245239/10000000000 : ℝ)|=(5476245239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5186884679/10000000000 : ℝ)|^4315 ≤ (42286263830649/100000000000000 : ℝ)^3291
        have hw : |(5186884679/10000000000 : ℝ)|=(5186884679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s2_1 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5365046057/10000000000 : ℝ)*x 0 + (-135804369/625000000 : ℝ)*x 1 + (5186885053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5365046057/10000000000 : ℝ)^4315 ≤ (8840153192079/20000000000000 : ℝ)^3291 := by
    have hnat : (5365046057 : ℕ)^4315*20000000000000^3291 ≤ 8840153192079^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365046057 10000000000 8840153192079 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135804369/625000000 : ℝ)^4315 ≤ (211140096797/1562500000000 : ℝ)^3291 := by
    have hnat : (135804369 : ℕ)^4315*1562500000000^3291 ≤ 211140096797^3291*625000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135804369 625000000 211140096797 1562500000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5186885053/10000000000 : ℝ)^4315 ≤ (21143133914207/50000000000000 : ℝ)^3291 := by
    have hnat : (5186885053 : ℕ)^4315*50000000000000^3291 ≤ 21143133914207^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186885053 10000000000 21143133914207 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5365046057/10000000000 : ℝ), (-135804369/625000000 : ℝ), (5186885053/10000000000 : ℝ)] ![(8840153192079/20000000000000 : ℝ), (211140096797/1562500000000 : ℝ), (21143133914207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5365046057/10000000000 : ℝ)|^4315 ≤ (8840153192079/20000000000000 : ℝ)^3291
        have hw : |(5365046057/10000000000 : ℝ)|=(5365046057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135804369/625000000 : ℝ)|^4315 ≤ (211140096797/1562500000000 : ℝ)^3291
        have hw : |(-135804369/625000000 : ℝ)|=(135804369/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5186885053/10000000000 : ℝ)|^4315 ≤ (21143133914207/50000000000000 : ℝ)^3291
        have hw : |(5186885053/10000000000 : ℝ)|=(5186885053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s2_2 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5365046123/10000000000 : ℝ)*x 0 + (207475399/400000000 : ℝ)*x 1 + (-2172869919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5365046123/10000000000 : ℝ)^4315 ≤ (8840153334667/20000000000000 : ℝ)^3291 := by
    have hnat : (5365046123 : ℕ)^4315*20000000000000^3291 ≤ 8840153334667^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365046123 10000000000 8840153334667 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207475399/400000000 : ℝ)^4315 ≤ (1321445843583/3125000000000 : ℝ)^3291 := by
    have hnat : (207475399 : ℕ)^4315*3125000000000^3291 ≤ 1321445843583^3291*400000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207475399 400000000 1321445843583 3125000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172869919/10000000000 : ℝ)^4315 ≤ (6756483158659/50000000000000 : ℝ)^3291 := by
    have hnat : (2172869919 : ℕ)^4315*50000000000000^3291 ≤ 6756483158659^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172869919 10000000000 6756483158659 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5365046123/10000000000 : ℝ), (207475399/400000000 : ℝ), (-2172869919/10000000000 : ℝ)] ![(8840153334667/20000000000000 : ℝ), (1321445843583/3125000000000 : ℝ), (6756483158659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5365046123/10000000000 : ℝ)|^4315 ≤ (8840153334667/20000000000000 : ℝ)^3291
        have hw : |(5365046123/10000000000 : ℝ)|=(5365046123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207475399/400000000 : ℝ)|^4315 ≤ (1321445843583/3125000000000 : ℝ)^3291
        have hw : |(207475399/400000000 : ℝ)|=(207475399/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2172869919/10000000000 : ℝ)|^4315 ≤ (6756483158659/50000000000000 : ℝ)^3291
        have hw : |(-2172869919/10000000000 : ℝ)|=(2172869919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s2_3 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (431732451/1000000000 : ℝ)*x 0 + (502844219/1250000000 : ℝ)*x 1 + (1157951351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431732451/1000000000 : ℝ)^4315 ≤ (16621918809573/50000000000000 : ℝ)^3291 := by
    have hnat : (431732451 : ℕ)^4315*50000000000000^3291 ≤ 16621918809573^3291*1000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431732451 1000000000 16621918809573 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502844219/1250000000 : ℝ)^4315 ≤ (30301929029457/100000000000000 : ℝ)^3291 := by
    have hnat : (502844219 : ℕ)^4315*100000000000000^3291 ≤ 30301929029457^3291*1250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502844219 1250000000 30301929029457 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1157951351/2500000000 : ℝ)^4315 ≤ (36454233341943/100000000000000 : ℝ)^3291 := by
    have hnat : (1157951351 : ℕ)^4315*100000000000000^3291 ≤ 36454233341943^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157951351 2500000000 36454233341943 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431732451/1000000000 : ℝ), (502844219/1250000000 : ℝ), (1157951351/2500000000 : ℝ)] ![(16621918809573/50000000000000 : ℝ), (30301929029457/100000000000000 : ℝ), (36454233341943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431732451/1000000000 : ℝ)|^4315 ≤ (16621918809573/50000000000000 : ℝ)^3291
        have hw : |(431732451/1000000000 : ℝ)|=(431732451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502844219/1250000000 : ℝ)|^4315 ≤ (30301929029457/100000000000000 : ℝ)^3291
        have hw : |(502844219/1250000000 : ℝ)|=(502844219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1157951351/2500000000 : ℝ)|^4315 ≤ (36454233341943/100000000000000 : ℝ)^3291
        have hw : |(1157951351/2500000000 : ℝ)|=(1157951351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s2_4 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2023522611/10000000000 : ℝ)*x 0 + (5188674087/10000000000 : ℝ)*x 1 + (2737219963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2023522611/10000000000 : ℝ)^4315 ≤ (96159564393/781250000000 : ℝ)^3291 := by
    have hnat : (2023522611 : ℕ)^4315*781250000000^3291 ≤ 96159564393^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023522611 10000000000 96159564393 781250000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5188674087/10000000000 : ℝ)^4315 ≤ (42305392216427/100000000000000 : ℝ)^3291 := by
    have hnat : (5188674087 : ℕ)^4315*100000000000000^3291 ≤ 42305392216427^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188674087 10000000000 42305392216427 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2737219963/5000000000 : ℝ)^4315 ≤ (45386183524559/100000000000000 : ℝ)^3291 := by
    have hnat : (2737219963 : ℕ)^4315*100000000000000^3291 ≤ 45386183524559^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737219963 5000000000 45386183524559 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2023522611/10000000000 : ℝ), (5188674087/10000000000 : ℝ), (2737219963/5000000000 : ℝ)] ![(96159564393/781250000000 : ℝ), (42305392216427/100000000000000 : ℝ), (45386183524559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2023522611/10000000000 : ℝ)|^4315 ≤ (96159564393/781250000000 : ℝ)^3291
        have hw : |(-2023522611/10000000000 : ℝ)|=(2023522611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5188674087/10000000000 : ℝ)|^4315 ≤ (42305392216427/100000000000000 : ℝ)^3291
        have hw : |(5188674087/10000000000 : ℝ)|=(5188674087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2737219963/5000000000 : ℝ)|^4315 ≤ (45386183524559/100000000000000 : ℝ)^3291
        have hw : |(2737219963/5000000000 : ℝ)|=(2737219963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s2_5 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290359103/10000000000 : ℝ)*x 0 + (-942657369/5000000000 : ℝ)*x 1 + (1368609973/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290359103/10000000000 : ℝ)^4315 ≤ (10848935238471/25000000000000 : ℝ)^3291 := by
    have hnat : (5290359103 : ℕ)^4315*25000000000000^3291 ≤ 10848935238471^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290359103 10000000000 10848935238471 25000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (942657369/5000000000 : ℝ)^4315 ≤ (1121807588273/10000000000000 : ℝ)^3291 := by
    have hnat : (942657369 : ℕ)^4315*10000000000000^3291 ≤ 1121807588273^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942657369 5000000000 1121807588273 10000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368609973/2500000000 : ℝ)^4315 ≤ (11346545788743/25000000000000 : ℝ)^3291 := by
    have hnat : (1368609973 : ℕ)^4315*25000000000000^3291 ≤ 11346545788743^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368609973 2500000000 11346545788743 25000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290359103/10000000000 : ℝ), (-942657369/5000000000 : ℝ), (1368609973/2500000000 : ℝ)] ![(10848935238471/25000000000000 : ℝ), (1121807588273/10000000000000 : ℝ), (11346545788743/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290359103/10000000000 : ℝ)|^4315 ≤ (10848935238471/25000000000000 : ℝ)^3291
        have hw : |(5290359103/10000000000 : ℝ)|=(5290359103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-942657369/5000000000 : ℝ)|^4315 ≤ (1121807588273/10000000000000 : ℝ)^3291
        have hw : |(-942657369/5000000000 : ℝ)|=(942657369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368609973/2500000000 : ℝ)|^4315 ≤ (11346545788743/25000000000000 : ℝ)^3291
        have hw : |(1368609973/2500000000 : ℝ)|=(1368609973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s2_6 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2645179541/5000000000 : ℝ)*x 0 + (5474439931/10000000000 : ℝ)*x 1 + (-1885314711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645179541/5000000000 : ℝ)^4315 ≤ (43395740728027/100000000000000 : ℝ)^3291 := by
    have hnat : (2645179541 : ℕ)^4315*100000000000000^3291 ≤ 43395740728027^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645179541 5000000000 43395740728027 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474439931/10000000000 : ℝ)^4315 ≤ (45386183578909/100000000000000 : ℝ)^3291 := by
    have hnat : (5474439931 : ℕ)^4315*100000000000000^3291 ≤ 45386183578909^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474439931 10000000000 45386183578909 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1885314711/10000000000 : ℝ)^4315 ≤ (2243615134417/20000000000000 : ℝ)^3291 := by
    have hnat : (1885314711 : ℕ)^4315*20000000000000^3291 ≤ 2243615134417^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885314711 10000000000 2243615134417 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645179541/5000000000 : ℝ), (5474439931/10000000000 : ℝ), (-1885314711/10000000000 : ℝ)] ![(43395740728027/100000000000000 : ℝ), (45386183578909/100000000000000 : ℝ), (2243615134417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645179541/5000000000 : ℝ)|^4315 ≤ (43395740728027/100000000000000 : ℝ)^3291
        have hw : |(2645179541/5000000000 : ℝ)|=(2645179541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474439931/10000000000 : ℝ)|^4315 ≤ (45386183578909/100000000000000 : ℝ)^3291
        have hw : |(5474439931/10000000000 : ℝ)|=(5474439931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1885314711/10000000000 : ℝ)|^4315 ≤ (2243615134417/20000000000000 : ℝ)^3291
        have hw : |(-1885314711/10000000000 : ℝ)|=(1885314711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s2_7 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2158727957/5000000000 : ℝ)*x 0 + (925607923/2000000000 : ℝ)*x 1 + (2013276513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158727957/5000000000 : ℝ)^4315 ≤ (16622582140159/50000000000000 : ℝ)^3291 := by
    have hnat : (2158727957 : ℕ)^4315*50000000000000^3291 ≤ 16622582140159^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158727957 5000000000 16622582140159 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (925607923/2000000000 : ℝ)^4315 ≤ (36415377921047/100000000000000 : ℝ)^3291 := by
    have hnat : (925607923 : ℕ)^4315*100000000000000^3291 ≤ 36415377921047^3291*2000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925607923 2000000000 36415377921047 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013276513/5000000000 : ℝ)^4315 ≤ (7584864446071/25000000000000 : ℝ)^3291 := by
    have hnat : (2013276513 : ℕ)^4315*25000000000000^3291 ≤ 7584864446071^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013276513 5000000000 7584864446071 25000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158727957/5000000000 : ℝ), (925607923/2000000000 : ℝ), (2013276513/5000000000 : ℝ)] ![(16622582140159/50000000000000 : ℝ), (36415377921047/100000000000000 : ℝ), (7584864446071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158727957/5000000000 : ℝ)|^4315 ≤ (16622582140159/50000000000000 : ℝ)^3291
        have hw : |(2158727957/5000000000 : ℝ)|=(2158727957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(925607923/2000000000 : ℝ)|^4315 ≤ (36415377921047/100000000000000 : ℝ)^3291
        have hw : |(925607923/2000000000 : ℝ)|=(925607923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2013276513/5000000000 : ℝ)|^4315 ≤ (7584864446071/25000000000000 : ℝ)^3291
        have hw : |(2013276513/5000000000 : ℝ)|=(2013276513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1355_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3873/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (621/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16053/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3873/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (701/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3873/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (701/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3873/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (701/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3873/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (701/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3873/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (701/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3873/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (701/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (701/10000 : ℝ) ^ (2157/512 : ℝ) ≤ (171413993234901/12500000000000000000 : ℝ) := by
    have hpowers : (701/10000 : ℝ)^2157 ≤ (171413993234901/12500000000000000000 : ℝ)^512 := by
      have hnat : (701 : ℕ)^2157*12500000000000000000^512 ≤ 171413993234901^512*10000^2157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        701 10000 171413993234901 12500000000000000000 2157 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (701/10000 : ℝ)) (X := (171413993234901/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3873/20000 : ℝ) ^ (2157/512 : ℝ) ≤ (3098366135183613/3125000000000000000 : ℝ) := by
    have hpowers : (3873/20000 : ℝ)^2157 ≤ (3098366135183613/3125000000000000000 : ℝ)^512 := by
      have hnat : (3873 : ℕ)^2157*3125000000000000000^512 ≤ 3098366135183613^512*20000^2157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3873 20000 3098366135183613 3125000000000000000 2157 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3873/20000 : ℝ)) (X := (3098366135183613/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250171413993234901/6250000000000000000 : ℝ) ≤ (625004068755063/625000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (6250171413993234901/6250000000000000000 : ℝ)^512 ≤ (625004068755063/625000000000000 : ℝ)^2157 := by
      have hnat : (6250171413993234901 : ℕ)^512*625000000000000^2157 ≤ 625004068755063^2157*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250171413993234901 6250000000000000000 625004068755063 625000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625004068755063/625000000000000 : ℝ)) (X := (6250171413993234901/6250000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12512564878533969353/12500000000000000000 : ℝ) ≤ (10002385073134693/10000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (12512564878533969353/12500000000000000000 : ℝ)^512 ≤ (10002385073134693/10000000000000000 : ℝ)^2157 := by
      have hnat : (12512564878533969353 : ℕ)^512*10000000000000000^2157 ≤ 10002385073134693^2157*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12512564878533969353 12500000000000000000 10002385073134693 10000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002385073134693/10000000000000000 : ℝ)) (X := (12512564878533969353/12500000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1565598366135183613/1562500000000000000 : ℝ) ≤ (5002352523094189/5000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (1565598366135183613/1562500000000000000 : ℝ)^512 ≤ (5002352523094189/5000000000000000 : ℝ)^2157 := by
      have hnat : (1565598366135183613 : ℕ)^512*5000000000000000^2157 ≤ 5002352523094189^2157*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1565598366135183613 1562500000000000000 5002352523094189 5000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002352523094189/5000000000000000 : ℝ)) (X := (1565598366135183613/1562500000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(171413993234901/12500000000000000000 : ℝ) ≤ ((882273416352058501/882500000000000000 : ℝ)+2*(66284944391/35300000000000 : ℝ)*(701/10000 : ℝ))^(2157/512 : ℝ) := by
    rw [show (882273416352058501/882500000000000000 : ℝ)+2*(66284944391/35300000000000 : ℝ)*(701/10000 : ℝ)=(625004068755063/625000000000000 : ℝ) by norm_num, show 1+2*(171413993234901/12500000000000000000 : ℝ)=(6250171413993234901/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3098366135183613/3125000000000000000 : ℝ)+(171413993234901/12500000000000000000 : ℝ) ≤ ((882273416352058501/882500000000000000 : ℝ)+(66284944391/35300000000000 : ℝ)*((3873/20000 : ℝ)+(701/10000 : ℝ)))^(2157/512 : ℝ) := by
    rw [show (882273416352058501/882500000000000000 : ℝ)+(66284944391/35300000000000 : ℝ)*((3873/20000 : ℝ)+(701/10000 : ℝ))=(10002385073134693/10000000000000000 : ℝ) by norm_num, show 1+(3098366135183613/3125000000000000000 : ℝ)+(171413993234901/12500000000000000000 : ℝ)=(12512564878533969353/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3098366135183613/3125000000000000000 : ℝ) ≤ ((882273416352058501/882500000000000000 : ℝ)+2*(66284944391/35300000000000 : ℝ)*(3873/20000 : ℝ))^(2157/512 : ℝ) := by
    rw [show (882273416352058501/882500000000000000 : ℝ)+2*(66284944391/35300000000000 : ℝ)*(3873/20000 : ℝ)=(5002352523094189/5000000000000000 : ℝ) by norm_num, show 1+2*(3098366135183613/3125000000000000000 : ℝ)=(1565598366135183613/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (882273416352058501/882500000000000000 : ℝ)*(X 1 0+X 2 0)+(66284944391/35300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (701/10000 : ℝ)) (hi := (3873/20000 : ℝ)) (c := (882273416352058501/882500000000000000 : ℝ)) (alpha := (66284944391/35300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (882273416352058501/882500000000000000 : ℝ)*(X 0 1+X 2 1)+(66284944391/35300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (701/10000 : ℝ)) (hi := (3873/20000 : ℝ)) (c := (882273416352058501/882500000000000000 : ℝ)) (alpha := (66284944391/35300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (882273416352058501/882500000000000000 : ℝ)*(X 0 2+X 1 2)+(66284944391/35300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (701/10000 : ℝ)) (hi := (3873/20000 : ℝ)) (c := (882273416352058501/882500000000000000 : ℝ)) (alpha := (66284944391/35300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2023460331/10000000000 : ℝ)*X 0 0+(5476245239/10000000000 : ℝ)*X 0 1+(5186884679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5365046057/10000000000 : ℝ)*X 1 0+(-135804369/625000000 : ℝ)*X 1 1+(5186885053/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5365046123/10000000000 : ℝ)*X 2 0+(207475399/400000000 : ℝ)*X 2 1+(-2172869919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((431732451/1000000000 : ℝ)*X 0 0+(502844219/1250000000 : ℝ)*X 0 1+(1157951351/2500000000 : ℝ)*X 0 2+(431732451/1000000000 : ℝ)*X 1 0+(502844219/1250000000 : ℝ)*X 1 1+(1157951351/2500000000 : ℝ)*X 1 2+(431732451/1000000000 : ℝ)*X 2 0+(502844219/1250000000 : ℝ)*X 2 1+(1157951351/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2023522611/10000000000 : ℝ)*X 0 0+(5188674087/10000000000 : ℝ)*X 0 1+(2737219963/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290359103/10000000000 : ℝ)*X 1 0+(-942657369/5000000000 : ℝ)*X 1 1+(1368609973/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2645179541/5000000000 : ℝ)*X 2 0+(5474439931/10000000000 : ℝ)*X 2 1+(-1885314711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2158727957/5000000000 : ℝ)*X 0 0+(925607923/2000000000 : ℝ)*X 0 1+(2013276513/5000000000 : ℝ)*X 0 2+(2158727957/5000000000 : ℝ)*X 1 0+(925607923/2000000000 : ℝ)*X 1 1+(2013276513/5000000000 : ℝ)*X 1 2+(2158727957/5000000000 : ℝ)*X 2 0+(925607923/2000000000 : ℝ)*X 2 1+(2013276513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41328822070106403771/13789062500000000000000000 : ℝ) := by norm_num
    linear_combination (406013061/100000000000000 : ℝ)*(base19) + (214669731/50000000000000 : ℝ)*(base23) + (16642531/25000000000000 : ℝ)*(upper3) + (2573577/25000000000000 : ℝ)*(upper4) + (1975723/4000000000000 : ℝ)*(upper5) + (318613579990339/12500000000000 : ℝ)*(major0) + (318613579990339/12500000000000 : ℝ)*(major1) + (318613579990339/12500000000000 : ℝ)*(major2) + (1727952453884639/50000000000000 : ℝ)*(sp0) + (69118269548321/2000000000000 : ℝ)*(sp1) + (215994590880603/6250000000000 : ℝ)*(sp2) + (820949960666323/50000000000000 : ℝ)*(sp3) + (8975659833/100000000000000 : ℝ)*(sp4) + (843794101/25000000000000 : ℝ)*(sp7) + (32838065930181/2000000000000 : ℝ)*(f.failure) + (3455913883429111/100000000000000 : ℝ)*(f.sum) + (6625865303883/1765000000000000000000000000 : ℝ)*base66 + (73885260482359411/11031250000000000000000000000000 : ℝ)*base68 + (40375826443296839/11031250000000000000000000000000 : ℝ)*base69 + (69201109343390661/11031250000000000000000000000000 : ℝ)*base72 + (2054368507097/441250000000000000000000000 : ℝ)*base74 + (11609121528265661/11031250000000000000000000000000 : ℝ)*base76 + (75354377892171839/11031250000000000000000000000000 : ℝ)*base77 + (85599876014171839/11031250000000000000000000000000 : ℝ)*base79 + (1167423635531/220625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1029007/100000000000000000000 : ℝ)*base89 + (1029007/100000000000000000000 : ℝ)*base91 + (1029007/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (783700372972789397001/353000000000000000000000000 : ℝ) := by norm_num
    linear_combination (582309323/100000000000000 : ℝ)*(base19) + (333405343/50000000000000 : ℝ)*(base23) + (64669227/100000000000000 : ℝ)*(upper3) + (3657829/10000000000000 : ℝ)*(lower4) + (4769637/50000000000000 : ℝ)*(upper5) + (25809574033947/1000000000000 : ℝ)*(major0) + (25809574033947/1000000000000 : ℝ)*(major1) + (25809574033947/1000000000000 : ℝ)*(major2) + (325086703/5000000000000 : ℝ)*(sp1) + (1714731351/20000000000000 : ℝ)*(sp2) + (1749683463042593/50000000000000 : ℝ)*(sp4) + (874839960510451/25000000000000 : ℝ)*(sp5) + (1749678842808873/50000000000000 : ℝ)*(sp6) + (415636951675099/25000000000000 : ℝ)*(sp7) + (415636951675099/25000000000000 : ℝ)*(f.failure) + (1749683463042593/50000000000000 : ℝ)*(f.sum) + (968327616327/176500000000000000000000000 : ℝ)*base66 + (6522357083693447/882500000000000000000000000000 : ℝ)*base67 + (9256102211368447/882500000000000000000000000000 : ℝ)*base69 + (2045325731961553/882500000000000000000000000000 : ℝ)*base72 + (53910861737/44125000000000000000000000 : ℝ)*base73 + (1182737992471553/882500000000000000000000000000 : ℝ)*base76 + (2796566287625947/882500000000000000000000000000 : ℝ)*base77 + (68679300199053/882500000000000000000000000000 : ℝ)*base80 + (303921831531/70600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (659153/1250000000000000000000 : ℝ)*base89 + (659153/1250000000000000000000 : ℝ)*base91 + (659153/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1355_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3873/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (621/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16053/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1355_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1355_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (621/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16053/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1355_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1355_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1355_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (621/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16053/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1355_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
