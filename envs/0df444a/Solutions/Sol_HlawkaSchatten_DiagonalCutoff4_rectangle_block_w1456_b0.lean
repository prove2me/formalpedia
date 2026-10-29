-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1456_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:01:06.602983+00:00
-- url     : https://prove2.me/submissions/4e6d4f03-04e2-48ca-bb13-d67c2e039351

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
theorem support_rectangle_w1456_s0_0 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1743627797/10000000000 : ℝ)*x 0 + (5949118269/10000000000 : ℝ)*x 1 + (2418686033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1743627797/10000000000 : ℝ)^69 ≤ (10291026578589/100000000000000 : ℝ)^53 := by
    have hnat : (1743627797 : ℕ)^69*100000000000000^53 ≤ 10291026578589^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1743627797 10000000000 10291026578589 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5949118269/10000000000 : ℝ)^69 ≤ (12714603786877/25000000000000 : ℝ)^53 := by
    have hnat : (5949118269 : ℕ)^69*25000000000000^53 ≤ 12714603786877^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5949118269 10000000000 12714603786877 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2418686033/5000000000 : ℝ)^69 ≤ (19425279127177/50000000000000 : ℝ)^53 := by
    have hnat : (2418686033 : ℕ)^69*50000000000000^53 ≤ 19425279127177^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418686033 5000000000 19425279127177 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1743627797/10000000000 : ℝ), (5949118269/10000000000 : ℝ), (2418686033/5000000000 : ℝ)] ![(10291026578589/100000000000000 : ℝ), (12714603786877/25000000000000 : ℝ), (19425279127177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1743627797/10000000000 : ℝ)|^69 ≤ (10291026578589/100000000000000 : ℝ)^53
        have hw : |(-1743627797/10000000000 : ℝ)|=(1743627797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5949118269/10000000000 : ℝ)|^69 ≤ (12714603786877/25000000000000 : ℝ)^53
        have hw : |(5949118269/10000000000 : ℝ)|=(5949118269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2418686033/5000000000 : ℝ)|^69 ≤ (19425279127177/50000000000000 : ℝ)^53
        have hw : |(2418686033/5000000000 : ℝ)|=(2418686033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s0_1 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5489101177/10000000000 : ℝ)*x 0 + (-2370484301/10000000000 : ℝ)*x 1 + (2418685993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5489101177/10000000000 : ℝ)^69 ≤ (9159886561021/20000000000000 : ℝ)^53 := by
    have hnat : (5489101177 : ℕ)^69*20000000000000^53 ≤ 9159886561021^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489101177 10000000000 9159886561021 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2370484301/10000000000 : ℝ)^69 ≤ (959375609733/6250000000000 : ℝ)^53 := by
    have hnat : (2370484301 : ℕ)^69*6250000000000^53 ≤ 959375609733^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2370484301 10000000000 959375609733 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2418685993/5000000000 : ℝ)^69 ≤ (38850557417883/100000000000000 : ℝ)^53 := by
    have hnat : (2418685993 : ℕ)^69*100000000000000^53 ≤ 38850557417883^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418685993 5000000000 38850557417883 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5489101177/10000000000 : ℝ), (-2370484301/10000000000 : ℝ), (2418685993/5000000000 : ℝ)] ![(9159886561021/20000000000000 : ℝ), (959375609733/6250000000000 : ℝ), (38850557417883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5489101177/10000000000 : ℝ)|^69 ≤ (9159886561021/20000000000000 : ℝ)^53
        have hw : |(5489101177/10000000000 : ℝ)|=(5489101177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2370484301/10000000000 : ℝ)|^69 ≤ (959375609733/6250000000000 : ℝ)^53
        have hw : |(-2370484301/10000000000 : ℝ)|=(2370484301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2418685993/5000000000 : ℝ)|^69 ≤ (38850557417883/100000000000000 : ℝ)^53
        have hw : |(2418685993/5000000000 : ℝ)|=(2418685993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s0_2 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5489100821/10000000000 : ℝ)*x 0 + (4837371983/10000000000 : ℝ)*x 1 + (-592621191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5489100821/10000000000 : ℝ)^69 ≤ (9159885787607/20000000000000 : ℝ)^53 := by
    have hnat : (5489100821 : ℕ)^69*20000000000000^53 ≤ 9159885787607^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489100821 10000000000 9159885787607 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4837371983/10000000000 : ℝ)^69 ≤ (7770111477303/20000000000000 : ℝ)^53 := by
    have hnat : (4837371983 : ℕ)^69*20000000000000^53 ≤ 7770111477303^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4837371983 10000000000 7770111477303 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (592621191/2500000000 : ℝ)^69 ≤ (15350013658973/100000000000000 : ℝ)^53 := by
    have hnat : (592621191 : ℕ)^69*100000000000000^53 ≤ 15350013658973^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592621191 2500000000 15350013658973 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5489100821/10000000000 : ℝ), (4837371983/10000000000 : ℝ), (-592621191/2500000000 : ℝ)] ![(9159885787607/20000000000000 : ℝ), (7770111477303/20000000000000 : ℝ), (15350013658973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5489100821/10000000000 : ℝ)|^69 ≤ (9159885787607/20000000000000 : ℝ)^53
        have hw : |(5489100821/10000000000 : ℝ)|=(5489100821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4837371983/10000000000 : ℝ)|^69 ≤ (7770111477303/20000000000000 : ℝ)^53
        have hw : |(4837371983/10000000000 : ℝ)|=(4837371983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-592621191/2500000000 : ℝ)|^69 ≤ (15350013658973/100000000000000 : ℝ)^53
        have hw : |(-592621191/2500000000 : ℝ)|=(592621191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s0_3 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4162152971/10000000000 : ℝ)*x 0 + (620557477/2000000000 : ℝ)*x 1 + (2765839833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4162152971/10000000000 : ℝ)^69 ≤ (7986108198527/25000000000000 : ℝ)^53 := by
    have hnat : (4162152971 : ℕ)^69*25000000000000^53 ≤ 7986108198527^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162152971 10000000000 7986108198527 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620557477/2000000000 : ℝ)^69 ≤ (5448270635057/25000000000000 : ℝ)^53 := by
    have hnat : (620557477 : ℕ)^69*25000000000000^53 ≤ 5448270635057^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620557477 2000000000 5448270635057 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2765839833/5000000000 : ℝ)^69 ≤ (46262484645709/100000000000000 : ℝ)^53 := by
    have hnat : (2765839833 : ℕ)^69*100000000000000^53 ≤ 46262484645709^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2765839833 5000000000 46262484645709 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4162152971/10000000000 : ℝ), (620557477/2000000000 : ℝ), (2765839833/5000000000 : ℝ)] ![(7986108198527/25000000000000 : ℝ), (5448270635057/25000000000000 : ℝ), (46262484645709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4162152971/10000000000 : ℝ)|^69 ≤ (7986108198527/25000000000000 : ℝ)^53
        have hw : |(4162152971/10000000000 : ℝ)|=(4162152971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(620557477/2000000000 : ℝ)|^69 ≤ (5448270635057/25000000000000 : ℝ)^53
        have hw : |(620557477/2000000000 : ℝ)|=(620557477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2765839833/5000000000 : ℝ)|^69 ≤ (46262484645709/100000000000000 : ℝ)^53
        have hw : |(2765839833/5000000000 : ℝ)|=(2765839833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s0_4 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-436879389/2500000000 : ℝ)*x 0 + (2432878043/5000000000 : ℝ)*x 1 + (591972077/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436879389/2500000000 : ℝ)^69 ≤ (10320924911361/100000000000000 : ℝ)^53 := by
    have hnat : (436879389 : ℕ)^69*100000000000000^53 ≤ 10320924911361^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436879389 2500000000 10320924911361 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2432878043/5000000000 : ℝ)^69 ≤ (2446725058217/6250000000000 : ℝ)^53 := by
    have hnat : (2432878043 : ℕ)^69*6250000000000^53 ≤ 2446725058217^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2432878043 5000000000 2446725058217 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (591972077/1000000000 : ℝ)^69 ≤ (631643426747/1250000000000 : ℝ)^53 := by
    have hnat : (591972077 : ℕ)^69*1250000000000^53 ≤ 631643426747^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591972077 1000000000 631643426747 1250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436879389/2500000000 : ℝ), (2432878043/5000000000 : ℝ), (591972077/1000000000 : ℝ)] ![(10320924911361/100000000000000 : ℝ), (2446725058217/6250000000000 : ℝ), (631643426747/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436879389/2500000000 : ℝ)|^69 ≤ (10320924911361/100000000000000 : ℝ)^53
        have hw : |(-436879389/2500000000 : ℝ)|=(436879389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2432878043/5000000000 : ℝ)|^69 ≤ (2446725058217/6250000000000 : ℝ)^53
        have hw : |(2432878043/5000000000 : ℝ)|=(2432878043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(591972077/1000000000 : ℝ)|^69 ≤ (631643426747/1250000000000 : ℝ)^53
        have hw : |(591972077/1000000000 : ℝ)|=(591972077/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s0_5 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (259277327/500000000 : ℝ)*x 0 + (-25762719/200000000 : ℝ)*x 1 + (5919720841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259277327/500000000 : ℝ)^69 ≤ (42529940368203/100000000000000 : ℝ)^53 := by
    have hnat : (259277327 : ℕ)^69*100000000000000^53 ≤ 42529940368203^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259277327 500000000 42529940368203 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25762719/200000000 : ℝ)^69 ≤ (693858469241/10000000000000 : ℝ)^53 := by
    have hnat : (25762719 : ℕ)^69*10000000000000^53 ≤ 693858469241^53*200000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25762719 200000000 693858469241 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5919720841/10000000000 : ℝ)^69 ≤ (12632868732197/25000000000000 : ℝ)^53 := by
    have hnat : (5919720841 : ℕ)^69*25000000000000^53 ≤ 12632868732197^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5919720841 10000000000 12632868732197 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259277327/500000000 : ℝ), (-25762719/200000000 : ℝ), (5919720841/10000000000 : ℝ)] ![(42529940368203/100000000000000 : ℝ), (693858469241/10000000000000 : ℝ), (12632868732197/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259277327/500000000 : ℝ)|^69 ≤ (42529940368203/100000000000000 : ℝ)^53
        have hw : |(259277327/500000000 : ℝ)|=(259277327/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25762719/200000000 : ℝ)|^69 ≤ (693858469241/10000000000000 : ℝ)^53
        have hw : |(-25762719/200000000 : ℝ)|=(25762719/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5919720841/10000000000 : ℝ)|^69 ≤ (12632868732197/25000000000000 : ℝ)^53
        have hw : |(5919720841/10000000000 : ℝ)|=(5919720841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s0_6 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2592773287/5000000000 : ℝ)*x 0 + (5919720683/10000000000 : ℝ)*x 1 + (-1288136149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592773287/5000000000 : ℝ)^69 ≤ (21264970365621/50000000000000 : ℝ)^53 := by
    have hnat : (2592773287 : ℕ)^69*50000000000000^53 ≤ 21264970365621^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592773287 5000000000 21264970365621 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5919720683/10000000000 : ℝ)^69 ≤ (50531473172923/100000000000000 : ℝ)^53 := by
    have hnat : (5919720683 : ℕ)^69*100000000000000^53 ≤ 50531473172923^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5919720683 10000000000 50531473172923 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1288136149/10000000000 : ℝ)^69 ≤ (867323260991/12500000000000 : ℝ)^53 := by
    have hnat : (1288136149 : ℕ)^69*12500000000000^53 ≤ 867323260991^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288136149 10000000000 867323260991 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2592773287/5000000000 : ℝ), (5919720683/10000000000 : ℝ), (-1288136149/10000000000 : ℝ)] ![(21264970365621/50000000000000 : ℝ), (50531473172923/100000000000000 : ℝ), (867323260991/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2592773287/5000000000 : ℝ)|^69 ≤ (21264970365621/50000000000000 : ℝ)^53
        have hw : |(2592773287/5000000000 : ℝ)|=(2592773287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5919720683/10000000000 : ℝ)|^69 ≤ (50531473172923/100000000000000 : ℝ)^53
        have hw : |(5919720683/10000000000 : ℝ)|=(5919720683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1288136149/10000000000 : ℝ)|^69 ≤ (867323260991/12500000000000 : ℝ)^53
        have hw : |(-1288136149/10000000000 : ℝ)|=(1288136149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s0_7 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2085324841/5000000000 : ℝ)*x 0 + (5469666859/10000000000 : ℝ)*x 1 + (1583507061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2085324841/5000000000 : ℝ)^69 ≤ (32029357675777/100000000000000 : ℝ)^53 := by
    have hnat : (2085324841 : ℕ)^69*100000000000000^53 ≤ 32029357675777^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085324841 5000000000 32029357675777 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469666859/10000000000 : ℝ)^69 ≤ (1139710983063/2500000000000 : ℝ)^53 := by
    have hnat : (5469666859 : ℕ)^69*2500000000000^53 ≤ 1139710983063^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469666859 10000000000 1139710983063 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1583507061/5000000000 : ℝ)^69 ≤ (22382202987533/100000000000000 : ℝ)^53 := by
    have hnat : (1583507061 : ℕ)^69*100000000000000^53 ≤ 22382202987533^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583507061 5000000000 22382202987533 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2085324841/5000000000 : ℝ), (5469666859/10000000000 : ℝ), (1583507061/5000000000 : ℝ)] ![(32029357675777/100000000000000 : ℝ), (1139710983063/2500000000000 : ℝ), (22382202987533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2085324841/5000000000 : ℝ)|^69 ≤ (32029357675777/100000000000000 : ℝ)^53
        have hw : |(2085324841/5000000000 : ℝ)|=(2085324841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469666859/10000000000 : ℝ)|^69 ≤ (1139710983063/2500000000000 : ℝ)^53
        have hw : |(5469666859/10000000000 : ℝ)|=(5469666859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1583507061/5000000000 : ℝ)|^69 ≤ (22382202987533/100000000000000 : ℝ)^53
        have hw : |(1583507061/5000000000 : ℝ)|=(1583507061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1456_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2237/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26073/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4415/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4415 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4415*1^1024 ≤ 0^1024*1^4415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4415/1024 : ℝ) ≤ (1924297988538472703/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4415 ≤ (1924297988538472703/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4415*100000000000000000000^1024 ≤ 1924297988538472703^1024*5^4415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1924297988538472703 100000000000000000000 4415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1924297988538472703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4415 := by
      have hnat : (1 : ℕ)^1024*1^4415 ≤ 1^4415*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101924297988538472703/100000000000000000000 : ℝ) ≤ (10044305377771769/10000000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (101924297988538472703/100000000000000000000 : ℝ)^1024 ≤ (10044305377771769/10000000000000000 : ℝ)^4415 := by
      have hnat : (101924297988538472703 : ℕ)^1024*10000000000000000^4415 ≤ 10044305377771769^4415*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101924297988538472703 100000000000000000000 10044305377771769 10000000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10044305377771769/10000000000000000 : ℝ)) (X := (101924297988538472703/100000000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51924297988538472703/50000000000000000000 : ℝ) ≤ (5044305377771769/5000000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (51924297988538472703/50000000000000000000 : ℝ)^1024 ≤ (5044305377771769/5000000000000000 : ℝ)^4415 := by
      have hnat : (51924297988538472703 : ℕ)^1024*5000000000000000^4415 ≤ 5044305377771769^4415*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51924297988538472703 50000000000000000000 5044305377771769 5000000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5044305377771769/5000000000000000 : ℝ)) (X := (51924297988538472703/50000000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(44305377771769/4000000000000000 : ℝ)*(0 : ℝ))^(4415/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(44305377771769/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1924297988538472703/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(44305377771769/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4415/1024 : ℝ) := by
    rw [show (1 : ℝ)+(44305377771769/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10044305377771769/10000000000000000 : ℝ) by norm_num, show 1+(1924297988538472703/100000000000000000000 : ℝ)+(0 : ℝ)=(101924297988538472703/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1924297988538472703/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(44305377771769/4000000000000000 : ℝ)*(2/5 : ℝ))^(4415/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(44305377771769/4000000000000000 : ℝ)*(2/5 : ℝ)=(5044305377771769/5000000000000000 : ℝ) by norm_num, show 1+2*(1924297988538472703/100000000000000000000 : ℝ)=(51924297988538472703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(44305377771769/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (44305377771769/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(44305377771769/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (44305377771769/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(44305377771769/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (44305377771769/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1743627797/10000000000 : ℝ)*X 0 0+(5949118269/10000000000 : ℝ)*X 0 1+(2418686033/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5489101177/10000000000 : ℝ)*X 1 0+(-2370484301/10000000000 : ℝ)*X 1 1+(2418685993/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5489100821/10000000000 : ℝ)*X 2 0+(4837371983/10000000000 : ℝ)*X 2 1+(-592621191/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4162152971/10000000000 : ℝ)*X 0 0+(620557477/2000000000 : ℝ)*X 0 1+(2765839833/5000000000 : ℝ)*X 0 2+(4162152971/10000000000 : ℝ)*X 1 0+(620557477/2000000000 : ℝ)*X 1 1+(2765839833/5000000000 : ℝ)*X 1 2+(4162152971/10000000000 : ℝ)*X 2 0+(620557477/2000000000 : ℝ)*X 2 1+(2765839833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-436879389/2500000000 : ℝ)*X 0 0+(2432878043/5000000000 : ℝ)*X 0 1+(591972077/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((259277327/500000000 : ℝ)*X 1 0+(-25762719/200000000 : ℝ)*X 1 1+(5919720841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2592773287/5000000000 : ℝ)*X 2 0+(5919720683/10000000000 : ℝ)*X 2 1+(-1288136149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2085324841/5000000000 : ℝ)*X 0 0+(5469666859/10000000000 : ℝ)*X 0 1+(1583507061/5000000000 : ℝ)*X 0 2+(2085324841/5000000000 : ℝ)*X 1 0+(5469666859/10000000000 : ℝ)*X 1 1+(1583507061/5000000000 : ℝ)*X 1 2+(2085324841/5000000000 : ℝ)*X 2 0+(5469666859/10000000000 : ℝ)*X 2 1+(1583507061/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (81210009860703805299699/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (152500023/100000000000000 : ℝ)*(base1) + (34846133/100000000000000 : ℝ)*(base16) + (325456031/100000000000000 : ℝ)*(base19) + (301965257/100000000000000 : ℝ)*(base23) + (13474709/50000000000000 : ℝ)*(upper3) + (327799437966781/50000000000000 : ℝ)*(major0) + (327799437966781/50000000000000 : ℝ)*(major1) + (327799437966781/50000000000000 : ℝ)*(major2) + (449743265386113/50000000000000 : ℝ)*(sp0) + (449743208778413/50000000000000 : ℝ)*(sp1) + (899486475893733/100000000000000 : ℝ)*(sp2) + (102927630124789/25000000000000 : ℝ)*(sp3) + (199793393/50000000000000 : ℝ)*(sp4) + (246868941/100000000000000 : ℝ)*(sp7) + (10292772996703/2500000000000 : ℝ)*(f.failure) + (89948677785899/10000000000000 : ℝ)*(f.sum) + (188527811605589/100000000000000000000000000000 : ℝ)*base65 + (893491667805589/200000000000000000000000000000 : ℝ)*base67 + (1428455454805589/200000000000000000000000000000 : ℝ)*base69 + (612780933605589/200000000000000000000000000000 : ℝ)*base71 + (446553146305589/100000000000000000000000000000 : ℝ)*base73 + (89916994805589/200000000000000000000000000000 : ℝ)*base75 + (721166815405589/200000000000000000000000000000 : ℝ)*base77 + (361410438005589/200000000000000000000000000000 : ℝ)*base79 + (541525353005589/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (159799/25000000000000000000 : ℝ)*base90 + (159799/25000000000000000000 : ℝ)*base92 + (159799/25000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1141588489123578835103409/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1305751743/100000000000000 : ℝ)*(base19) + (658854027/50000000000000 : ℝ)*(base23) + (132173729/100000000000000 : ℝ)*(base32) + (49529421/25000000000000 : ℝ)*(upper3) + (117012573/100000000000000 : ℝ)*(upper5) + (691539762312271/100000000000000 : ℝ)*(major0) + (691539762312271/100000000000000 : ℝ)*(major1) + (691539762312271/100000000000000 : ℝ)*(major2) + (1577134497/50000000000000 : ℝ)*(sp1) + (3252248701/100000000000000 : ℝ)*(sp2) + (474398910752011/50000000000000 : ℝ)*(sp4) + (189758672296657/20000000000000 : ℝ)*(sp5) + (474396625773633/50000000000000 : ℝ)*(sp6) + (108570345170509/25000000000000 : ℝ)*(sp7) + (86856302571153/20000000000000 : ℝ)*(f.failure) + (474398910752011/50000000000000 : ℝ)*(f.sum) + (185820682077399/200000000000000000000000000000 : ℝ)*base65 + (2170872019677399/400000000000000000000000000000 : ℝ)*base67 + (1761058586722601/400000000000000000000000000000 : ℝ)*base70 + (618760190077399/400000000000000000000000000000 : ℝ)*base71 + (712163950077399/200000000000000000000000000000 : ℝ)*base73 + (199058281677399/400000000000000000000000000000 : ℝ)*base75 + (2690336043277399/400000000000000000000000000000 : ℝ)*base77 + (4755724472077399/400000000000000000000000000000 : ℝ)*base79 + (1096339292722601/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (706649/200000000000000000000 : ℝ)*base90 + (706649/200000000000000000000 : ℝ)*base92 + (706649/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1456_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2237/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26073/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1456_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1456_s1_0 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1912170903/10000000000 : ℝ)*x 0 + (174831087/312500000 : ℝ)*x 1 + (5083799193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1912170903/10000000000 : ℝ)^69 ≤ (580228572679/5000000000000 : ℝ)^53 := by
    have hnat : (1912170903 : ℕ)^69*5000000000000^53 ≤ 580228572679^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912170903 10000000000 580228572679 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174831087/312500000 : ℝ)^69 ≤ (46948672697937/100000000000000 : ℝ)^53 := by
    have hnat : (174831087 : ℕ)^69*100000000000000^53 ≤ 46948672697937^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174831087 312500000 46948672697937 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5083799193/10000000000 : ℝ)^69 ≤ (41446755837039/100000000000000 : ℝ)^53 := by
    have hnat : (5083799193 : ℕ)^69*100000000000000^53 ≤ 41446755837039^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083799193 10000000000 41446755837039 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1912170903/10000000000 : ℝ), (174831087/312500000 : ℝ), (5083799193/10000000000 : ℝ)] ![(580228572679/5000000000000 : ℝ), (46948672697937/100000000000000 : ℝ), (41446755837039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1912170903/10000000000 : ℝ)|^69 ≤ (580228572679/5000000000000 : ℝ)^53
        have hw : |(-1912170903/10000000000 : ℝ)|=(1912170903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(174831087/312500000 : ℝ)|^69 ≤ (46948672697937/100000000000000 : ℝ)^53
        have hw : |(174831087/312500000 : ℝ)|=(174831087/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5083799193/10000000000 : ℝ)|^69 ≤ (41446755837039/100000000000000 : ℝ)^53
        have hw : |(5083799193/10000000000 : ℝ)|=(5083799193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s1_1 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5394119371/10000000000 : ℝ)*x 0 + (-1091144141/5000000000 : ℝ)*x 1 + (50838011/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394119371/10000000000 : ℝ)^69 ≤ (44770393211367/100000000000000 : ℝ)^53 := by
    have hnat : (5394119371 : ℕ)^69*100000000000000^53 ≤ 44770393211367^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394119371 10000000000 44770393211367 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091144141/5000000000 : ℝ)^69 ≤ (2756566138071/20000000000000 : ℝ)^53 := by
    have hnat : (1091144141 : ℕ)^69*20000000000000^53 ≤ 2756566138071^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091144141 5000000000 2756566138071 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50838011/100000000 : ℝ)^69 ≤ (8289355215553/20000000000000 : ℝ)^53 := by
    have hnat : (50838011 : ℕ)^69*20000000000000^53 ≤ 8289355215553^53*100000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50838011 100000000 8289355215553 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394119371/10000000000 : ℝ), (-1091144141/5000000000 : ℝ), (50838011/100000000 : ℝ)] ![(44770393211367/100000000000000 : ℝ), (2756566138071/20000000000000 : ℝ), (8289355215553/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394119371/10000000000 : ℝ)|^69 ≤ (44770393211367/100000000000000 : ℝ)^53
        have hw : |(5394119371/10000000000 : ℝ)|=(5394119371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091144141/5000000000 : ℝ)|^69 ≤ (2756566138071/20000000000000 : ℝ)^53
        have hw : |(-1091144141/5000000000 : ℝ)|=(1091144141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(50838011/100000000 : ℝ)|^69 ≤ (8289355215553/20000000000000 : ℝ)^53
        have hw : |(50838011/100000000 : ℝ)|=(50838011/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s1_2 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5394120967/10000000000 : ℝ)*x 0 + (2541899663/5000000000 : ℝ)*x 1 + (-87291539/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394120967/10000000000 : ℝ)^69 ≤ (8954082091379/20000000000000 : ℝ)^53 := by
    have hnat : (5394120967 : ℕ)^69*20000000000000^53 ≤ 8954082091379^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394120967 10000000000 8954082091379 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2541899663/5000000000 : ℝ)^69 ≤ (41446757248689/100000000000000 : ℝ)^53 := by
    have hnat : (2541899663 : ℕ)^69*100000000000000^53 ≤ 41446757248689^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541899663 5000000000 41446757248689 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87291539/400000000 : ℝ)^69 ≤ (6891416138641/50000000000000 : ℝ)^53 := by
    have hnat : (87291539 : ℕ)^69*50000000000000^53 ≤ 6891416138641^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87291539 400000000 6891416138641 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394120967/10000000000 : ℝ), (2541899663/5000000000 : ℝ), (-87291539/400000000 : ℝ)] ![(8954082091379/20000000000000 : ℝ), (41446757248689/100000000000000 : ℝ), (6891416138641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394120967/10000000000 : ℝ)|^69 ≤ (8954082091379/20000000000000 : ℝ)^53
        have hw : |(5394120967/10000000000 : ℝ)|=(5394120967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2541899663/5000000000 : ℝ)|^69 ≤ (41446757248689/100000000000000 : ℝ)^53
        have hw : |(2541899663/5000000000 : ℝ)|=(2541899663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-87291539/400000000 : ℝ)|^69 ≤ (6891416138641/50000000000000 : ℝ)^53
        have hw : |(-87291539/400000000 : ℝ)|=(87291539/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s1_3 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4271720687/10000000000 : ℝ)*x 0 + (936476279/2500000000 : ℝ)*x 1 + (2430931727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4271720687/10000000000 : ℝ)^69 ≤ (33043552086547/100000000000000 : ℝ)^53 := by
    have hnat : (4271720687 : ℕ)^69*100000000000000^53 ≤ 33043552086547^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271720687 10000000000 33043552086547 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (936476279/2500000000 : ℝ)^69 ≤ (13924807454977/50000000000000 : ℝ)^53 := by
    have hnat : (936476279 : ℕ)^69*50000000000000^53 ≤ 13924807454977^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936476279 2500000000 13924807454977 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2430931727/5000000000 : ℝ)^69 ≤ (4888354122009/12500000000000 : ℝ)^53 := by
    have hnat : (2430931727 : ℕ)^69*12500000000000^53 ≤ 4888354122009^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2430931727 5000000000 4888354122009 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4271720687/10000000000 : ℝ), (936476279/2500000000 : ℝ), (2430931727/5000000000 : ℝ)] ![(33043552086547/100000000000000 : ℝ), (13924807454977/50000000000000 : ℝ), (4888354122009/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4271720687/10000000000 : ℝ)|^69 ≤ (33043552086547/100000000000000 : ℝ)^53
        have hw : |(4271720687/10000000000 : ℝ)|=(4271720687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(936476279/2500000000 : ℝ)|^69 ≤ (13924807454977/50000000000000 : ℝ)^53
        have hw : |(936476279/2500000000 : ℝ)|=(936476279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2430931727/5000000000 : ℝ)|^69 ≤ (4888354122009/12500000000000 : ℝ)^53
        have hw : |(2430931727/5000000000 : ℝ)|=(2430931727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s1_4 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-956266867/5000000000 : ℝ)*x 0 + (5089663189/10000000000 : ℝ)*x 1 + (11177267/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (956266867/5000000000 : ℝ)^69 ≤ (1160743822091/10000000000000 : ℝ)^53 := by
    have hnat : (956266867 : ℕ)^69*10000000000000^53 ≤ 1160743822091^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956266867 5000000000 1160743822091 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5089663189/10000000000 : ℝ)^69 ≤ (830180131857/2000000000000 : ℝ)^53 := by
    have hnat : (5089663189 : ℕ)^69*2000000000000^53 ≤ 830180131857^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5089663189 10000000000 830180131857 2000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11177267/20000000 : ℝ)^69 ≤ (9376711035869/20000000000000 : ℝ)^53 := by
    have hnat : (11177267 : ℕ)^69*20000000000000^53 ≤ 9376711035869^53*20000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11177267 20000000 9376711035869 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-956266867/5000000000 : ℝ), (5089663189/10000000000 : ℝ), (11177267/20000000 : ℝ)] ![(1160743822091/10000000000000 : ℝ), (830180131857/2000000000000 : ℝ), (9376711035869/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-956266867/5000000000 : ℝ)|^69 ≤ (1160743822091/10000000000000 : ℝ)^53
        have hw : |(-956266867/5000000000 : ℝ)|=(956266867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5089663189/10000000000 : ℝ)|^69 ≤ (830180131857/2000000000000 : ℝ)^53
        have hw : |(5089663189/10000000000 : ℝ)|=(5089663189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11177267/20000000 : ℝ)|^69 ≤ (9376711035869/20000000000000 : ℝ)^53
        have hw : |(11177267/20000000 : ℝ)|=(11177267/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s1_5 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5260400719/10000000000 : ℝ)*x 0 + (-1677455167/10000000000 : ℝ)*x 1 + (1117726707/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260400719/10000000000 : ℝ)^69 ≤ (43330938694509/100000000000000 : ℝ)^53 := by
    have hnat : (5260400719 : ℕ)^69*100000000000000^53 ≤ 43330938694509^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260400719 10000000000 43330938694509 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1677455167/10000000000 : ℝ)^69 ≤ (4892752863141/50000000000000 : ℝ)^53 := by
    have hnat : (1677455167 : ℕ)^69*50000000000000^53 ≤ 4892752863141^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677455167 10000000000 4892752863141 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1117726707/2000000000 : ℝ)^69 ≤ (46883555561603/100000000000000 : ℝ)^53 := by
    have hnat : (1117726707 : ℕ)^69*100000000000000^53 ≤ 46883555561603^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117726707 2000000000 46883555561603 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260400719/10000000000 : ℝ), (-1677455167/10000000000 : ℝ), (1117726707/2000000000 : ℝ)] ![(43330938694509/100000000000000 : ℝ), (4892752863141/50000000000000 : ℝ), (46883555561603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260400719/10000000000 : ℝ)|^69 ≤ (43330938694509/100000000000000 : ℝ)^53
        have hw : |(5260400719/10000000000 : ℝ)|=(5260400719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1677455167/10000000000 : ℝ)|^69 ≤ (4892752863141/50000000000000 : ℝ)^53
        have hw : |(-1677455167/10000000000 : ℝ)|=(1677455167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1117726707/2000000000 : ℝ)|^69 ≤ (46883555561603/100000000000000 : ℝ)^53
        have hw : |(1117726707/2000000000 : ℝ)|=(1117726707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s1_6 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (164387519/312500000 : ℝ)*x 0 + (2794316749/5000000000 : ℝ)*x 1 + (-1677455377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164387519/312500000 : ℝ)^69 ≤ (43330937504157/100000000000000 : ℝ)^53 := by
    have hnat : (164387519 : ℕ)^69*100000000000000^53 ≤ 43330937504157^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164387519 312500000 43330937504157 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2794316749/5000000000 : ℝ)^69 ≤ (23441777578751/50000000000000 : ℝ)^53 := by
    have hnat : (2794316749 : ℕ)^69*50000000000000^53 ≤ 23441777578751^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794316749 5000000000 23441777578751 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1677455377/10000000000 : ℝ)^69 ≤ (9785507321151/100000000000000 : ℝ)^53 := by
    have hnat : (1677455377 : ℕ)^69*100000000000000^53 ≤ 9785507321151^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677455377 10000000000 9785507321151 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164387519/312500000 : ℝ), (2794316749/5000000000 : ℝ), (-1677455377/10000000000 : ℝ)] ![(43330937504157/100000000000000 : ℝ), (23441777578751/50000000000000 : ℝ), (9785507321151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164387519/312500000 : ℝ)|^69 ≤ (43330937504157/100000000000000 : ℝ)^53
        have hw : |(164387519/312500000 : ℝ)|=(164387519/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2794316749/5000000000 : ℝ)|^69 ≤ (23441777578751/50000000000000 : ℝ)^53
        have hw : |(2794316749/5000000000 : ℝ)|=(2794316749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1677455377/10000000000 : ℝ)|^69 ≤ (9785507321151/100000000000000 : ℝ)^53
        have hw : |(-1677455377/10000000000 : ℝ)|=(1677455377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s1_7 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4272514073/10000000000 : ℝ)*x 0 + (242452687/500000000 : ℝ)*x 1 + (1879463057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4272514073/10000000000 : ℝ)^69 ≤ (33051542215843/100000000000000 : ℝ)^53 := by
    have hnat : (4272514073 : ℕ)^69*100000000000000^53 ≤ 33051542215843^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272514073 10000000000 33051542215843 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242452687/500000000 : ℝ)^69 ≤ (7794549009223/20000000000000 : ℝ)^53 := by
    have hnat : (242452687 : ℕ)^69*20000000000000^53 ≤ 7794549009223^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242452687 500000000 7794549009223 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1879463057/5000000000 : ℝ)^69 ≤ (27975712719029/100000000000000 : ℝ)^53 := by
    have hnat : (1879463057 : ℕ)^69*100000000000000^53 ≤ 27975712719029^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879463057 5000000000 27975712719029 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4272514073/10000000000 : ℝ), (242452687/500000000 : ℝ), (1879463057/5000000000 : ℝ)] ![(33051542215843/100000000000000 : ℝ), (7794549009223/20000000000000 : ℝ), (27975712719029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4272514073/10000000000 : ℝ)|^69 ≤ (33051542215843/100000000000000 : ℝ)^53
        have hw : |(4272514073/10000000000 : ℝ)|=(4272514073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(242452687/500000000 : ℝ)|^69 ≤ (7794549009223/20000000000000 : ℝ)^53
        have hw : |(242452687/500000000 : ℝ)|=(242452687/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1879463057/5000000000 : ℝ)|^69 ≤ (27975712719029/100000000000000 : ℝ)^53
        have hw : |(1879463057/5000000000 : ℝ)|=(1879463057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1456_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (787/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1867/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2237/100000 : ℝ) ^ (4415/1024 : ℝ) ≤ (3832800504943/50000000000000000000 : ℝ) := by
    have hpowers : (2237/100000 : ℝ)^4415 ≤ (3832800504943/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2237 : ℕ)^4415*50000000000000000000^1024 ≤ 3832800504943^1024*100000^4415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2237 100000 3832800504943 50000000000000000000 4415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2237/100000 : ℝ)) (X := (3832800504943/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26073/100000 : ℝ) ^ (4415/1024 : ℝ) ≤ (304014174964910233/100000000000000000000 : ℝ) := by
    have hpowers : (26073/100000 : ℝ)^4415 ≤ (304014174964910233/100000000000000000000 : ℝ)^1024 := by
      have hnat : (26073 : ℕ)^4415*100000000000000000000^1024 ≤ 304014174964910233^1024*100000^4415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26073 100000 304014174964910233 100000000000000000000 4415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26073/100000 : ℝ)) (X := (304014174964910233/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000003832800504943/25000000000000000000 : ℝ) ≤ (2500000088896659/2500000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (25000003832800504943/25000000000000000000 : ℝ)^1024 ≤ (2500000088896659/2500000000000000 : ℝ)^4415 := by
      have hnat : (25000003832800504943 : ℕ)^1024*2500000000000000^4415 ≤ 2500000088896659^4415*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000003832800504943 25000000000000000000 2500000088896659 2500000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000088896659/2500000000000000 : ℝ)) (X := (25000003832800504943/25000000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100304021840565920119/100000000000000000000 : ℝ) ≤ (1250880395067693/1250000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (100304021840565920119/100000000000000000000 : ℝ)^1024 ≤ (1250880395067693/1250000000000000 : ℝ)^4415 := by
      have hnat : (100304021840565920119 : ℕ)^1024*1250000000000000^4415 ≤ 1250880395067693^4415*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100304021840565920119 100000000000000000000 1250880395067693 1250000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250880395067693/1250000000000000 : ℝ)) (X := (100304021840565920119/100000000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50304014174964910233/50000000000000000000 : ℝ) ≤ (2503521491374113/2500000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (50304014174964910233/50000000000000000000 : ℝ)^1024 ≤ (2503521491374113/2500000000000000 : ℝ)^4415 := by
      have hnat : (50304014174964910233 : ℕ)^1024*2500000000000000^4415 ≤ 2503521491374113^4415*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50304014174964910233 50000000000000000000 2503521491374113 2500000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503521491374113/2500000000000000 : ℝ)) (X := (50304014174964910233/50000000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3832800504943/50000000000000000000 : ℝ) ≤ ((29791062370799349663/29795000000000000000 : ℝ)+2*(1760701238727/595900000000000 : ℝ)*(2237/100000 : ℝ))^(4415/1024 : ℝ) := by
    rw [show (29791062370799349663/29795000000000000000 : ℝ)+2*(1760701238727/595900000000000 : ℝ)*(2237/100000 : ℝ)=(2500000088896659/2500000000000000 : ℝ) by norm_num, show 1+2*(3832800504943/50000000000000000000 : ℝ)=(25000003832800504943/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(304014174964910233/100000000000000000000 : ℝ)+(3832800504943/50000000000000000000 : ℝ) ≤ ((29791062370799349663/29795000000000000000 : ℝ)+(1760701238727/595900000000000 : ℝ)*((26073/100000 : ℝ)+(2237/100000 : ℝ)))^(4415/1024 : ℝ) := by
    rw [show (29791062370799349663/29795000000000000000 : ℝ)+(1760701238727/595900000000000 : ℝ)*((26073/100000 : ℝ)+(2237/100000 : ℝ))=(1250880395067693/1250000000000000 : ℝ) by norm_num, show 1+(304014174964910233/100000000000000000000 : ℝ)+(3832800504943/50000000000000000000 : ℝ)=(100304021840565920119/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(304014174964910233/100000000000000000000 : ℝ) ≤ ((29791062370799349663/29795000000000000000 : ℝ)+2*(1760701238727/595900000000000 : ℝ)*(26073/100000 : ℝ))^(4415/1024 : ℝ) := by
    rw [show (29791062370799349663/29795000000000000000 : ℝ)+2*(1760701238727/595900000000000 : ℝ)*(26073/100000 : ℝ)=(2503521491374113/2500000000000000 : ℝ) by norm_num, show 1+2*(304014174964910233/100000000000000000000 : ℝ)=(50304014174964910233/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29791062370799349663/29795000000000000000 : ℝ)*(X 1 0+X 2 0)+(1760701238727/595900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (2237/100000 : ℝ)) (hi := (26073/100000 : ℝ)) (c := (29791062370799349663/29795000000000000000 : ℝ)) (alpha := (1760701238727/595900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29791062370799349663/29795000000000000000 : ℝ)*(X 0 1+X 2 1)+(1760701238727/595900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (2237/100000 : ℝ)) (hi := (26073/100000 : ℝ)) (c := (29791062370799349663/29795000000000000000 : ℝ)) (alpha := (1760701238727/595900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29791062370799349663/29795000000000000000 : ℝ)*(X 0 2+X 1 2)+(1760701238727/595900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (2237/100000 : ℝ)) (hi := (26073/100000 : ℝ)) (c := (29791062370799349663/29795000000000000000 : ℝ)) (alpha := (1760701238727/595900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1912170903/10000000000 : ℝ)*X 0 0+(174831087/312500000 : ℝ)*X 0 1+(5083799193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5394119371/10000000000 : ℝ)*X 1 0+(-1091144141/5000000000 : ℝ)*X 1 1+(50838011/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5394120967/10000000000 : ℝ)*X 2 0+(2541899663/5000000000 : ℝ)*X 2 1+(-87291539/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4271720687/10000000000 : ℝ)*X 0 0+(936476279/2500000000 : ℝ)*X 0 1+(2430931727/5000000000 : ℝ)*X 0 2+(4271720687/10000000000 : ℝ)*X 1 0+(936476279/2500000000 : ℝ)*X 1 1+(2430931727/5000000000 : ℝ)*X 1 2+(4271720687/10000000000 : ℝ)*X 2 0+(936476279/2500000000 : ℝ)*X 2 1+(2430931727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-956266867/5000000000 : ℝ)*X 0 0+(5089663189/10000000000 : ℝ)*X 0 1+(11177267/20000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260400719/10000000000 : ℝ)*X 1 0+(-1677455167/10000000000 : ℝ)*X 1 1+(1117726707/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((164387519/312500000 : ℝ)*X 2 0+(2794316749/5000000000 : ℝ)*X 2 1+(-1677455377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4272514073/10000000000 : ℝ)*X 0 0+(242452687/500000000 : ℝ)*X 0 1+(1879463057/5000000000 : ℝ)*X 0 2+(4272514073/10000000000 : ℝ)*X 1 0+(242452687/500000000 : ℝ)*X 1 1+(1879463057/5000000000 : ℝ)*X 1 2+(4272514073/10000000000 : ℝ)*X 2 0+(242452687/500000000 : ℝ)*X 2 1+(1879463057/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3018492738805307599793966367/744875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (288792619/50000000000000 : ℝ)*(base19) + (265270061/25000000000000 : ℝ)*(base23) + (8988743/20000000000000 : ℝ)*(upper3) + (12913553/25000000000000 : ℝ)*(upper4) + (6508951/100000000000000 : ℝ)*(upper5) + (1426925472019207/100000000000000 : ℝ)*(major0) + (1426925472019207/100000000000000 : ℝ)*(major1) + (178365684002401/12500000000000 : ℝ)*(major2) + (978870372283759/50000000000000 : ℝ)*(sp0) + (1957752296747243/100000000000000 : ℝ)*(sp1) + (1957751813252237/100000000000000 : ℝ)*(sp2) + (112011730547421/12500000000000 : ℝ)*(sp3) + (12129764963/100000000000000 : ℝ)*(sp4) + (4090248291/100000000000000 : ℝ)*(sp7) + (896097934627659/100000000000000 : ℝ)*(f.failure) + (6117977732289/312500000000 : ℝ)*(f.sum) + (9614467270493/11918000000000000000000000000 : ℝ)*base66 + (21183994556530722759/2979500000000000000000000000000000 : ℝ)*base68 + (51411726899531307/6312500000000000000000000000000 : ℝ)*base69 + (23627336704698222759/2979500000000000000000000000000000 : ℝ)*base72 + (3037236081459/2383600000000000000000000000 : ℝ)*base74 + (26825209622906307/6312500000000000000000000000000 : ℝ)*base75 + (12703762559601572759/2979500000000000000000000000000000 : ℝ)*base78 + (4547855205035572759/2979500000000000000000000000000000 : ℝ)*base80 + (12798514408011/7448750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3671453/1000000000000000000000 : ℝ)*base89 + (3671453/1000000000000000000000 : ℝ)*base91 + (6328547/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1901790925666378099638605589/372437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1186363109/100000000000000 : ℝ)*(base19) + (233801671/20000000000000 : ℝ)*(base23) + (4416323/3125000000000 : ℝ)*(upper3) + (16624367/100000000000000 : ℝ)*(lower4) + (95404513/100000000000000 : ℝ)*(upper5) + (730362614263099/50000000000000 : ℝ)*(major0) + (730362614263099/50000000000000 : ℝ)*(major1) + (730362614263099/50000000000000 : ℝ)*(major2) + (154126527/2000000000000 : ℝ)*(sp1) + (7443898943/100000000000000 : ℝ)*(sp2) + (1002063185943389/50000000000000 : ℝ)*(sp4) + (2004117479197319/100000000000000 : ℝ)*(sp5) + (50102943974487/2500000000000 : ℝ)*(sp6) + (458661957477209/50000000000000 : ℝ)*(sp7) + (458661957477209/50000000000000 : ℝ)*(f.failure) + (1002063185943389/50000000000000 : ℝ)*(f.sum) + (9853377959957/3724375000000000000000000000 : ℝ)*base65 + (5368891279138135637/1489750000000000000000000000000000 : ℝ)*base67 + (1661355981110635637/1489750000000000000000000000000000 : ℝ)*base69 + (5503438999358885637/1489750000000000000000000000000000 : ℝ)*base71 + (79257862806081/29795000000000000000000000000 : ℝ)*base73 + (121300716073114363/1489750000000000000000000000000000 : ℝ)*base76 + (4723162310336385637/1489750000000000000000000000000000 : ℝ)*base77 + (906019768902135637/1489750000000000000000000000000000 : ℝ)*base79 + (22136961942181/29795000000000000000000000000 : ℝ)*base81 + (6073697/500000000000000000000 : ℝ)*base90 + (6073697/500000000000000000000 : ℝ)*base92 + (6073697/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1456_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (787/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1867/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1456_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1456_s2_0 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-388668223/2000000000 : ℝ)*x 0 + (272615347/500000000 : ℝ)*x 1 + (5205993481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (388668223/2000000000 : ℝ)^69 ≤ (11851447322443/100000000000000 : ℝ)^53 := by
    have hnat : (388668223 : ℕ)^69*100000000000000^53 ≤ 11851447322443^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388668223 2000000000 11851447322443 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272615347/500000000 : ℝ)^69 ≤ (11350039579941/25000000000000 : ℝ)^53 := by
    have hnat : (272615347 : ℕ)^69*25000000000000^53 ≤ 11350039579941^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272615347 500000000 11350039579941 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5205993481/10000000000 : ℝ)^69 ≤ (42748394353473/100000000000000 : ℝ)^53 := by
    have hnat : (5205993481 : ℕ)^69*100000000000000^53 ≤ 42748394353473^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205993481 10000000000 42748394353473 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-388668223/2000000000 : ℝ), (272615347/500000000 : ℝ), (5205993481/10000000000 : ℝ)] ![(11851447322443/100000000000000 : ℝ), (11350039579941/25000000000000 : ℝ), (42748394353473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-388668223/2000000000 : ℝ)|^69 ≤ (11851447322443/100000000000000 : ℝ)^53
        have hw : |(-388668223/2000000000 : ℝ)|=(388668223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272615347/500000000 : ℝ)|^69 ≤ (11350039579941/25000000000000 : ℝ)^53
        have hw : |(272615347/500000000 : ℝ)|=(272615347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5205993481/10000000000 : ℝ)|^69 ≤ (42748394353473/100000000000000 : ℝ)^53
        have hw : |(5205993481/10000000000 : ℝ)|=(5205993481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s2_1 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (669807101/1250000000 : ℝ)*x 0 + (-1034961067/5000000000 : ℝ)*x 1 + (1301498367/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669807101/1250000000 : ℝ)^69 ≤ (2219271384197/5000000000000 : ℝ)^53 := by
    have hnat : (669807101 : ℕ)^69*5000000000000^53 ≤ 2219271384197^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669807101 1250000000 2219271384197 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034961067/5000000000 : ℝ)^69 ≤ (12866178084237/100000000000000 : ℝ)^53 := by
    have hnat : (1034961067 : ℕ)^69*100000000000000^53 ≤ 12866178084237^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034961067 5000000000 12866178084237 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301498367/2500000000 : ℝ)^69 ≤ (85496788429/200000000000 : ℝ)^53 := by
    have hnat : (1301498367 : ℕ)^69*200000000000^53 ≤ 85496788429^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301498367 2500000000 85496788429 200000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669807101/1250000000 : ℝ), (-1034961067/5000000000 : ℝ), (1301498367/2500000000 : ℝ)] ![(2219271384197/5000000000000 : ℝ), (12866178084237/100000000000000 : ℝ), (85496788429/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669807101/1250000000 : ℝ)|^69 ≤ (2219271384197/5000000000000 : ℝ)^53
        have hw : |(669807101/1250000000 : ℝ)|=(669807101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1034961067/5000000000 : ℝ)|^69 ≤ (12866178084237/100000000000000 : ℝ)^53
        have hw : |(-1034961067/5000000000 : ℝ)|=(1034961067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301498367/2500000000 : ℝ)|^69 ≤ (85496788429/200000000000 : ℝ)^53
        have hw : |(1301498367/2500000000 : ℝ)|=(1301498367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s2_2 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5358456917/10000000000 : ℝ)*x 0 + (2602996669/5000000000 : ℝ)*x 1 + (-2069922161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358456917/10000000000 : ℝ)^69 ≤ (2219271442969/5000000000000 : ℝ)^53 := by
    have hnat : (5358456917 : ℕ)^69*5000000000000^53 ≤ 2219271442969^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358456917 10000000000 2219271442969 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2602996669/5000000000 : ℝ)^69 ≤ (21374196412381/50000000000000 : ℝ)^53 := by
    have hnat : (2602996669 : ℕ)^69*50000000000000^53 ≤ 21374196412381^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602996669 5000000000 21374196412381 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069922161/10000000000 : ℝ)^69 ≤ (1608272287841/12500000000000 : ℝ)^53 := by
    have hnat : (2069922161 : ℕ)^69*12500000000000^53 ≤ 1608272287841^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069922161 10000000000 1608272287841 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358456917/10000000000 : ℝ), (2602996669/5000000000 : ℝ), (-2069922161/10000000000 : ℝ)] ![(2219271442969/5000000000000 : ℝ), (21374196412381/50000000000000 : ℝ), (1608272287841/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358456917/10000000000 : ℝ)|^69 ≤ (2219271442969/5000000000000 : ℝ)^53
        have hw : |(5358456917/10000000000 : ℝ)|=(5358456917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2602996669/5000000000 : ℝ)|^69 ≤ (21374196412381/50000000000000 : ℝ)^53
        have hw : |(2602996669/5000000000 : ℝ)|=(2602996669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2069922161/10000000000 : ℝ)|^69 ≤ (1608272287841/12500000000000 : ℝ)^53
        have hw : |(-2069922161/10000000000 : ℝ)|=(2069922161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s2_3 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1073445967/2500000000 : ℝ)*x 0 + (403219791/1000000000 : ℝ)*x 1 + (2285166147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073445967/2500000000 : ℝ)^69 ≤ (16632957734547/50000000000000 : ℝ)^53 := by
    have hnat : (1073445967 : ℕ)^69*50000000000000^53 ≤ 16632957734547^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073445967 2500000000 16632957734547 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403219791/1000000000 : ℝ)^69 ≤ (15326046394091/50000000000000 : ℝ)^53 := by
    have hnat : (403219791 : ℕ)^69*50000000000000^53 ≤ 15326046394091^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403219791 1000000000 15326046394091 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285166147/5000000000 : ℝ)^69 ≤ (4510248965851/12500000000000 : ℝ)^53 := by
    have hnat : (2285166147 : ℕ)^69*12500000000000^53 ≤ 4510248965851^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285166147 5000000000 4510248965851 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073445967/2500000000 : ℝ), (403219791/1000000000 : ℝ), (2285166147/5000000000 : ℝ)] ![(16632957734547/50000000000000 : ℝ), (15326046394091/50000000000000 : ℝ), (4510248965851/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073445967/2500000000 : ℝ)|^69 ≤ (16632957734547/50000000000000 : ℝ)^53
        have hw : |(1073445967/2500000000 : ℝ)|=(1073445967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(403219791/1000000000 : ℝ)|^69 ≤ (15326046394091/50000000000000 : ℝ)^53
        have hw : |(403219791/1000000000 : ℝ)|=(403219791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2285166147/5000000000 : ℝ)|^69 ≤ (4510248965851/12500000000000 : ℝ)^53
        have hw : |(2285166147/5000000000 : ℝ)|=(2285166147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s2_4 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1943381269/10000000000 : ℝ)*x 0 + (5207366799/10000000000 : ℝ)*x 1 + (2725461569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1943381269/10000000000 : ℝ)^69 ≤ (11851766127897/100000000000000 : ℝ)^53 := by
    have hnat : (1943381269 : ℕ)^69*100000000000000^53 ≤ 11851766127897^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943381269 10000000000 11851766127897 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5207366799/10000000000 : ℝ)^69 ≤ (5345384512881/12500000000000 : ℝ)^53 := by
    have hnat : (5207366799 : ℕ)^69*12500000000000^53 ≤ 5345384512881^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207366799 10000000000 5345384512881 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725461569/5000000000 : ℝ)^69 ≤ (45385157755121/100000000000000 : ℝ)^53 := by
    have hnat : (2725461569 : ℕ)^69*100000000000000^53 ≤ 45385157755121^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725461569 5000000000 45385157755121 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1943381269/10000000000 : ℝ), (5207366799/10000000000 : ℝ), (2725461569/5000000000 : ℝ)] ![(11851766127897/100000000000000 : ℝ), (5345384512881/12500000000000 : ℝ), (45385157755121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1943381269/10000000000 : ℝ)|^69 ≤ (11851766127897/100000000000000 : ℝ)^53
        have hw : |(-1943381269/10000000000 : ℝ)|=(1943381269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5207366799/10000000000 : ℝ)|^69 ≤ (5345384512881/12500000000000 : ℝ)^53
        have hw : |(5207366799/10000000000 : ℝ)|=(5207366799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725461569/5000000000 : ℝ)|^69 ≤ (45385157755121/100000000000000 : ℝ)^53
        have hw : |(2725461569/5000000000 : ℝ)|=(2725461569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s2_5 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (529424803/1000000000 : ℝ)*x 0 + (-28515479/156250000 : ℝ)*x 1 + (2725462239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529424803/1000000000 : ℝ)^69 ≤ (21847132827357/50000000000000 : ℝ)^53 := by
    have hnat : (529424803 : ℕ)^69*50000000000000^53 ≤ 21847132827357^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529424803 1000000000 21847132827357 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28515479/156250000 : ℝ)^69 ≤ (87364496417/800000000000 : ℝ)^53 := by
    have hnat : (28515479 : ℕ)^69*800000000000^53 ≤ 87364496417^53*156250000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28515479 156250000 87364496417 800000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725462239/5000000000 : ℝ)^69 ≤ (45385172280311/100000000000000 : ℝ)^53 := by
    have hnat : (2725462239 : ℕ)^69*100000000000000^53 ≤ 45385172280311^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725462239 5000000000 45385172280311 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529424803/1000000000 : ℝ), (-28515479/156250000 : ℝ), (2725462239/5000000000 : ℝ)] ![(21847132827357/50000000000000 : ℝ), (87364496417/800000000000 : ℝ), (45385172280311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529424803/1000000000 : ℝ)|^69 ≤ (21847132827357/50000000000000 : ℝ)^53
        have hw : |(529424803/1000000000 : ℝ)|=(529424803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28515479/156250000 : ℝ)|^69 ≤ (87364496417/800000000000 : ℝ)^53
        have hw : |(-28515479/156250000 : ℝ)|=(28515479/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725462239/5000000000 : ℝ)|^69 ≤ (45385172280311/100000000000000 : ℝ)^53
        have hw : |(2725462239/5000000000 : ℝ)|=(2725462239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s2_6 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5294247009/10000000000 : ℝ)*x 0 + (43607389/80000000 : ℝ)*x 1 + (-1824993251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294247009/10000000000 : ℝ)^69 ≤ (43694254684399/100000000000000 : ℝ)^53 := by
    have hnat : (5294247009 : ℕ)^69*100000000000000^53 ≤ 43694254684399^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294247009 10000000000 43694254684399 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43607389/80000000 : ℝ)^69 ≤ (11346290758513/25000000000000 : ℝ)^53 := by
    have hnat : (43607389 : ℕ)^69*25000000000000^53 ≤ 11346290758513^53*80000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43607389 80000000 11346290758513 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1824993251/10000000000 : ℝ)^69 ≤ (2730145567029/25000000000000 : ℝ)^53 := by
    have hnat : (1824993251 : ℕ)^69*25000000000000^53 ≤ 2730145567029^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824993251 10000000000 2730145567029 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294247009/10000000000 : ℝ), (43607389/80000000 : ℝ), (-1824993251/10000000000 : ℝ)] ![(43694254684399/100000000000000 : ℝ), (11346290758513/25000000000000 : ℝ), (2730145567029/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294247009/10000000000 : ℝ)|^69 ≤ (43694254684399/100000000000000 : ℝ)^53
        have hw : |(5294247009/10000000000 : ℝ)|=(5294247009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43607389/80000000 : ℝ)|^69 ≤ (11346290758513/25000000000000 : ℝ)^53
        have hw : |(43607389/80000000 : ℝ)|=(43607389/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1824993251/10000000000 : ℝ)|^69 ≤ (2730145567029/25000000000000 : ℝ)^53
        have hw : |(-1824993251/10000000000 : ℝ)|=(1824993251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s2_7 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4293873139/10000000000 : ℝ)*x 0 + (1141833883/2500000000 : ℝ)*x 1 + (807043709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4293873139/10000000000 : ℝ)^69 ≤ (33266815887333/100000000000000 : ℝ)^53 := by
    have hnat : (4293873139 : ℕ)^69*100000000000000^53 ≤ 33266815887333^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4293873139 10000000000 33266815887333 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141833883/2500000000 : ℝ)^69 ≤ (36051193535869/100000000000000 : ℝ)^53 := by
    have hnat : (1141833883 : ℕ)^69*100000000000000^53 ≤ 36051193535869^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141833883 2500000000 36051193535869 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (807043709/2000000000 : ℝ)^69 ≤ (958812205079/3125000000000 : ℝ)^53 := by
    have hnat : (807043709 : ℕ)^69*3125000000000^53 ≤ 958812205079^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807043709 2000000000 958812205079 3125000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4293873139/10000000000 : ℝ), (1141833883/2500000000 : ℝ), (807043709/2000000000 : ℝ)] ![(33266815887333/100000000000000 : ℝ), (36051193535869/100000000000000 : ℝ), (958812205079/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4293873139/10000000000 : ℝ)|^69 ≤ (33266815887333/100000000000000 : ℝ)^53
        have hw : |(4293873139/10000000000 : ℝ)|=(4293873139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1141833883/2500000000 : ℝ)|^69 ≤ (36051193535869/100000000000000 : ℝ)^53
        have hw : |(1141833883/2500000000 : ℝ)|=(1141833883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(807043709/2000000000 : ℝ)|^69 ≤ (958812205079/3125000000000 : ℝ)^53
        have hw : |(807043709/2000000000 : ℝ)|=(807043709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1456_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1867/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (787/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10507/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (393/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1867/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (787/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1867/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (787/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1867/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (787/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1867/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (787/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1867/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (787/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1867/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (787/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (787/10000 : ℝ) ^ (4415/1024 : ℝ) ≤ (868838760409787/50000000000000000000 : ℝ) := by
    have hpowers : (787/10000 : ℝ)^4415 ≤ (868838760409787/50000000000000000000 : ℝ)^1024 := by
      have hnat : (787 : ℕ)^4415*50000000000000000000^1024 ≤ 868838760409787^1024*10000^4415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        787 10000 868838760409787 50000000000000000000 4415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (787/10000 : ℝ)) (X := (868838760409787/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1867/10000 : ℝ) ^ (4415/1024 : ℝ) ≤ (36015682459641461/50000000000000000000 : ℝ) := by
    have hpowers : (1867/10000 : ℝ)^4415 ≤ (36015682459641461/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1867 : ℕ)^4415*50000000000000000000^1024 ≤ 36015682459641461^1024*10000^4415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1867 10000 36015682459641461 50000000000000000000 4415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1867/10000 : ℝ)) (X := (36015682459641461/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000868838760409787/25000000000000000000 : ℝ) ≤ (1250010075640053/1250000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (25000868838760409787/25000000000000000000 : ℝ)^1024 ≤ (1250010075640053/1250000000000000 : ℝ)^4415 := by
      have hnat : (25000868838760409787 : ℕ)^1024*1250000000000000^4415 ≤ 1250010075640053^4415*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000868838760409787 25000000000000000000 1250010075640053 1250000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250010075640053/1250000000000000 : ℝ)) (X := (25000868838760409787/25000000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3127305282576253203/3125000000000000000 : ℝ) ≤ (5000855244718923/5000000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (3127305282576253203/3125000000000000000 : ℝ)^1024 ≤ (5000855244718923/5000000000000000 : ℝ)^4415 := by
      have hnat : (3127305282576253203 : ℕ)^1024*5000000000000000^4415 ≤ 5000855244718923^4415*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127305282576253203 3125000000000000000 5000855244718923 5000000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000855244718923/5000000000000000 : ℝ)) (X := (3127305282576253203/3125000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25036015682459641461/25000000000000000000 : ℝ) ≤ (2500835093438817/2500000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (25036015682459641461/25000000000000000000 : ℝ)^1024 ≤ (2500835093438817/2500000000000000 : ℝ)^4415 := by
      have hnat : (25036015682459641461 : ℕ)^1024*2500000000000000^4415 ≤ 2500835093438817^4415*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25036015682459641461 25000000000000000000 2500835093438817 2500000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500835093438817/2500000000000000 : ℝ)) (X := (25036015682459641461/25000000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(868838760409787/50000000000000000000 : ℝ) ≤ ((899793467967869641/900000000000000000 : ℝ)+2*(271647386237/180000000000000 : ℝ)*(787/10000 : ℝ))^(4415/1024 : ℝ) := by
    rw [show (899793467967869641/900000000000000000 : ℝ)+2*(271647386237/180000000000000 : ℝ)*(787/10000 : ℝ)=(1250010075640053/1250000000000000 : ℝ) by norm_num, show 1+2*(868838760409787/50000000000000000000 : ℝ)=(25000868838760409787/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36015682459641461/50000000000000000000 : ℝ)+(868838760409787/50000000000000000000 : ℝ) ≤ ((899793467967869641/900000000000000000 : ℝ)+(271647386237/180000000000000 : ℝ)*((1867/10000 : ℝ)+(787/10000 : ℝ)))^(4415/1024 : ℝ) := by
    rw [show (899793467967869641/900000000000000000 : ℝ)+(271647386237/180000000000000 : ℝ)*((1867/10000 : ℝ)+(787/10000 : ℝ))=(5000855244718923/5000000000000000 : ℝ) by norm_num, show 1+(36015682459641461/50000000000000000000 : ℝ)+(868838760409787/50000000000000000000 : ℝ)=(3127305282576253203/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36015682459641461/50000000000000000000 : ℝ) ≤ ((899793467967869641/900000000000000000 : ℝ)+2*(271647386237/180000000000000 : ℝ)*(1867/10000 : ℝ))^(4415/1024 : ℝ) := by
    rw [show (899793467967869641/900000000000000000 : ℝ)+2*(271647386237/180000000000000 : ℝ)*(1867/10000 : ℝ)=(2500835093438817/2500000000000000 : ℝ) by norm_num, show 1+2*(36015682459641461/50000000000000000000 : ℝ)=(25036015682459641461/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (899793467967869641/900000000000000000 : ℝ)*(X 1 0+X 2 0)+(271647386237/180000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (787/10000 : ℝ)) (hi := (1867/10000 : ℝ)) (c := (899793467967869641/900000000000000000 : ℝ)) (alpha := (271647386237/180000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (899793467967869641/900000000000000000 : ℝ)*(X 0 1+X 2 1)+(271647386237/180000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (787/10000 : ℝ)) (hi := (1867/10000 : ℝ)) (c := (899793467967869641/900000000000000000 : ℝ)) (alpha := (271647386237/180000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (899793467967869641/900000000000000000 : ℝ)*(X 0 2+X 1 2)+(271647386237/180000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (787/10000 : ℝ)) (hi := (1867/10000 : ℝ)) (c := (899793467967869641/900000000000000000 : ℝ)) (alpha := (271647386237/180000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-388668223/2000000000 : ℝ)*X 0 0+(272615347/500000000 : ℝ)*X 0 1+(5205993481/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669807101/1250000000 : ℝ)*X 1 0+(-1034961067/5000000000 : ℝ)*X 1 1+(1301498367/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358456917/10000000000 : ℝ)*X 2 0+(2602996669/5000000000 : ℝ)*X 2 1+(-2069922161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1073445967/2500000000 : ℝ)*X 0 0+(403219791/1000000000 : ℝ)*X 0 1+(2285166147/5000000000 : ℝ)*X 0 2+(1073445967/2500000000 : ℝ)*X 1 0+(403219791/1000000000 : ℝ)*X 1 1+(2285166147/5000000000 : ℝ)*X 1 2+(1073445967/2500000000 : ℝ)*X 2 0+(403219791/1000000000 : ℝ)*X 2 1+(2285166147/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1943381269/10000000000 : ℝ)*X 0 0+(5207366799/10000000000 : ℝ)*X 0 1+(2725461569/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529424803/1000000000 : ℝ)*X 1 0+(-28515479/156250000 : ℝ)*X 1 1+(2725462239/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294247009/10000000000 : ℝ)*X 2 0+(43607389/80000000 : ℝ)*X 2 1+(-1824993251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4293873139/10000000000 : ℝ)*X 0 0+(1141833883/2500000000 : ℝ)*X 0 1+(807043709/2000000000 : ℝ)*X 0 2+(4293873139/10000000000 : ℝ)*X 1 0+(1141833883/2500000000 : ℝ)*X 1 1+(807043709/2000000000 : ℝ)*X 1 2+(4293873139/10000000000 : ℝ)*X 2 0+(1141833883/2500000000 : ℝ)*X 2 1+(807043709/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18993597972788605083203561/2500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (785341509/50000000000000 : ℝ)*(base19) + (1566472999/100000000000000 : ℝ)*(base23) + (46508939/100000000000000 : ℝ)*(lower2) + (215428367/100000000000000 : ℝ)*(upper3) + (13800299/10000000000000 : ℝ)*(upper5) + (1479551206218637/50000000000000 : ℝ)*(major0) + (1479551206218637/50000000000000 : ℝ)*(major1) + (1479551206218637/50000000000000 : ℝ)*(major2) + (405988987893607/10000000000000 : ℝ)*(sp0) + (1014977510053889/25000000000000 : ℝ)*(sp1) + (2029955022212787/50000000000000 : ℝ)*(sp2) + (929140877178141/50000000000000 : ℝ)*(sp3) + (2716495313/12500000000000 : ℝ)*(sp4) + (11206371713/100000000000000 : ℝ)*(sp7) + (371658592145599/20000000000000 : ℝ)*(f.failure) + (2029955805449287/50000000000000 : ℝ)*(f.sum) + (6950165542469/4500000000000000000000000000 : ℝ)*base65 + (77366127215544317/45000000000000000000000000000000 : ℝ)*base67 + (462226995519455683/45000000000000000000000000000000 : ℝ)*base70 + (323620810760544317/45000000000000000000000000000000 : ℝ)*base71 + (8620465245031/4500000000000000000000000000 : ℝ)*base74 + (687686489889455683/45000000000000000000000000000000 : ℝ)*base76 + (123087755810544317/45000000000000000000000000000000 : ℝ)*base77 + (187121328995544317/45000000000000000000000000000000 : ℝ)*base79 + (12238012843469/4500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (551433/200000000000000000000 : ℝ)*base89 + (551433/200000000000000000000 : ℝ)*base91 + (551433/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (198789833464292017440483/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (323934579/50000000000000 : ℝ)*(base19) + (71817367/100000000000000 : ℝ)*(base23) + (58623659/50000000000000 : ℝ)*(upper3) + (21182181/6250000000000 : ℝ)*(lower4) + (14962822955837/500000000000 : ℝ)*(major0) + (14962822955837/500000000000 : ℝ)*(major1) + (14962822955837/500000000000 : ℝ)*(major2) + (5284650689/100000000000000 : ℝ)*(sp0) + (34993125927/100000000000000 : ℝ)*(sp1) + (2450202119/20000000000000 : ℝ)*(sp3) + (4105816687755817/100000000000000 : ℝ)*(sp4) + (205289316570571/5000000000000 : ℝ)*(sp5) + (4105821900589139/100000000000000 : ℝ)*(sp6) + (1879294693864571/100000000000000 : ℝ)*(sp7) + (939653472437583/50000000000000 : ℝ)*(f.failure) + (2052910986203253/50000000000000 : ℝ)*(f.sum) + (27562873339/2812500000000000000000000 : ℝ)*base65 + (5333931993639517/450000000000000000000000000000 : ℝ)*base67 + (3097710266889517/450000000000000000000000000000 : ℝ)*base69 + (8269188042639517/450000000000000000000000000000 : ℝ)*base71 + (42555108589/45000000000000000000000000 : ℝ)*base73 + (7618126118439517/450000000000000000000000000000 : ℝ)*base75 + (3634335806889517/450000000000000000000000000000 : ℝ)*base77 + (9465783649239517/450000000000000000000000000000 : ℝ)*base79 + (26778569749/45000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6264839/500000000000000000000 : ℝ)*base90 + (6264839/500000000000000000000 : ℝ)*base92 + (6264839/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1456_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1867/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (787/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10507/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (393/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1456_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1456_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10507/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (393/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1456_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1456_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1456_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10507/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (393/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1456_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
