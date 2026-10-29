-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1566_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:25:56.60067+00:00
-- url     : https://prove2.me/submissions/9242f79b-1ca2-469b-a0f5-b80fa0622b0e

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
theorem support_rectangle_w1566_box_0 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1586641677/10000000000 : ℝ)*x 0 + (134925549/250000000 : ℝ)*x 1 + (134925529/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1586641677/10000000000 : ℝ)^4629 ≤ (293917168147/3125000000000 : ℝ)^3605 := by
    have hnat : (1586641677 : ℕ)^4629*3125000000000^3605 ≤ 293917168147^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586641677 10000000000 293917168147 3125000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134925549/250000000 : ℝ)^4629 ≤ (45297329611843/100000000000000 : ℝ)^3605 := by
    have hnat : (134925549 : ℕ)^4629*100000000000000^3605 ≤ 45297329611843^3605*250000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134925549 250000000 45297329611843 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134925529/250000000 : ℝ)^4629 ≤ (22648660495097/50000000000000 : ℝ)^3605 := by
    have hnat : (134925529 : ℕ)^4629*50000000000000^3605 ≤ 22648660495097^3605*250000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134925529 250000000 22648660495097 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1586641677/10000000000 : ℝ), (134925549/250000000 : ℝ), (134925529/250000000 : ℝ)] ![(293917168147/3125000000000 : ℝ), (45297329611843/100000000000000 : ℝ), (22648660495097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1586641677/10000000000 : ℝ)|^4629 ≤ (293917168147/3125000000000 : ℝ)^3605
        have hw : |(-1586641677/10000000000 : ℝ)|=(1586641677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134925549/250000000 : ℝ)|^4629 ≤ (45297329611843/100000000000000 : ℝ)^3605
        have hw : |(134925549/250000000 : ℝ)|=(134925549/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134925529/250000000 : ℝ)|^4629 ≤ (22648660495097/50000000000000 : ℝ)^3605
        have hw : |(134925529/250000000 : ℝ)|=(134925529/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_1 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054228091/2000000000 : ℝ)*x 0 + (-880803649/5000000000 : ℝ)*x 1 + (5397021657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054228091/2000000000 : ℝ)^4629 ≤ (43945216284263/100000000000000 : ℝ)^3605 := by
    have hnat : (1054228091 : ℕ)^4629*100000000000000^3605 ≤ 43945216284263^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054228091 2000000000 43945216284263 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880803649/5000000000 : ℝ)^4629 ≤ (10757457357457/100000000000000 : ℝ)^3605 := by
    have hnat : (880803649 : ℕ)^4629*100000000000000^3605 ≤ 10757457357457^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880803649 5000000000 10757457357457 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397021657/10000000000 : ℝ)^4629 ≤ (45297326346393/100000000000000 : ℝ)^3605 := by
    have hnat : (5397021657 : ℕ)^4629*100000000000000^3605 ≤ 45297326346393^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397021657 10000000000 45297326346393 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054228091/2000000000 : ℝ), (-880803649/5000000000 : ℝ), (5397021657/10000000000 : ℝ)] ![(43945216284263/100000000000000 : ℝ), (10757457357457/100000000000000 : ℝ), (45297326346393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054228091/2000000000 : ℝ)|^4629 ≤ (43945216284263/100000000000000 : ℝ)^3605
        have hw : |(1054228091/2000000000 : ℝ)|=(1054228091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-880803649/5000000000 : ℝ)|^4629 ≤ (10757457357457/100000000000000 : ℝ)^3605
        have hw : |(-880803649/5000000000 : ℝ)|=(880803649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397021657/10000000000 : ℝ)|^4629 ≤ (45297326346393/100000000000000 : ℝ)^3605
        have hw : |(5397021657/10000000000 : ℝ)|=(5397021657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_2 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271141027/10000000000 : ℝ)*x 0 + (2698510761/5000000000 : ℝ)*x 1 + (-1761606701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271141027/10000000000 : ℝ)^4629 ≤ (8789044481511/20000000000000 : ℝ)^3605 := by
    have hnat : (5271141027 : ℕ)^4629*20000000000000^3605 ≤ 8789044481511^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271141027 10000000000 8789044481511 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698510761/5000000000 : ℝ)^4629 ≤ (4529732489149/10000000000000 : ℝ)^3605 := by
    have hnat : (2698510761 : ℕ)^4629*10000000000000^3605 ≤ 4529732489149^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698510761 5000000000 4529732489149 10000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1761606701/10000000000 : ℝ)^4629 ≤ (10757452676261/100000000000000 : ℝ)^3605 := by
    have hnat : (1761606701 : ℕ)^4629*100000000000000^3605 ≤ 10757452676261^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761606701 10000000000 10757452676261 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271141027/10000000000 : ℝ), (2698510761/5000000000 : ℝ), (-1761606701/10000000000 : ℝ)] ![(8789044481511/20000000000000 : ℝ), (4529732489149/10000000000000 : ℝ), (10757452676261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271141027/10000000000 : ℝ)|^4629 ≤ (8789044481511/20000000000000 : ℝ)^3605
        have hw : |(5271141027/10000000000 : ℝ)|=(5271141027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698510761/5000000000 : ℝ)|^4629 ≤ (4529732489149/10000000000000 : ℝ)^3605
        have hw : |(2698510761/5000000000 : ℝ)|=(2698510761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1761606701/10000000000 : ℝ)|^4629 ≤ (10757452676261/100000000000000 : ℝ)^3605
        have hw : |(-1761606701/10000000000 : ℝ)|=(1761606701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_3 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1111527371/2500000000 : ℝ)*x 0 + (830301597/2000000000 : ℝ)*x 1 + (83030181/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1111527371/2500000000 : ℝ)^4629 ≤ (35317417527927/100000000000000 : ℝ)^3605 := by
    have hnat : (1111527371 : ℕ)^4629*100000000000000^3605 ≤ 35317417527927^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111527371 2500000000 35317417527927 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (830301597/2000000000 : ℝ)^4629 ≤ (6468257179727/20000000000000 : ℝ)^3605 := by
    have hnat : (830301597 : ℕ)^4629*20000000000000^3605 ≤ 6468257179727^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830301597 2000000000 6468257179727 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83030181/200000000 : ℝ)^4629 ≤ (6468259310381/20000000000000 : ℝ)^3605 := by
    have hnat : (83030181 : ℕ)^4629*20000000000000^3605 ≤ 6468259310381^3605*200000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83030181 200000000 6468259310381 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1111527371/2500000000 : ℝ), (830301597/2000000000 : ℝ), (83030181/200000000 : ℝ)] ![(35317417527927/100000000000000 : ℝ), (6468257179727/20000000000000 : ℝ), (6468259310381/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1111527371/2500000000 : ℝ)|^4629 ≤ (35317417527927/100000000000000 : ℝ)^3605
        have hw : |(1111527371/2500000000 : ℝ)|=(1111527371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(830301597/2000000000 : ℝ)|^4629 ≤ (6468257179727/20000000000000 : ℝ)^3605
        have hw : |(830301597/2000000000 : ℝ)|=(830301597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(83030181/200000000 : ℝ)|^4629 ≤ (6468259310381/20000000000000 : ℝ)^3605
        have hw : |(83030181/200000000 : ℝ)|=(83030181/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_4 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2000941553/10000000000 : ℝ)*x 0 + (5244981889/10000000000 : ℝ)*x 1 + (655622783/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2000941553/10000000000 : ℝ)^4629 ≤ (12669226014483/100000000000000 : ℝ)^3605 := by
    have hnat : (2000941553 : ℕ)^4629*100000000000000^3605 ≤ 12669226014483^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000941553 10000000000 12669226014483 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244981889/10000000000 : ℝ)^4629 ≤ (8733076996353/20000000000000 : ℝ)^3605 := by
    have hnat : (5244981889 : ℕ)^4629*20000000000000^3605 ≤ 8733076996353^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244981889 10000000000 8733076996353 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655622783/1250000000 : ℝ)^4629 ≤ (10916347247623/25000000000000 : ℝ)^3605 := by
    have hnat : (655622783 : ℕ)^4629*25000000000000^3605 ≤ 10916347247623^3605*1250000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655622783 1250000000 10916347247623 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2000941553/10000000000 : ℝ), (5244981889/10000000000 : ℝ), (655622783/1250000000 : ℝ)] ![(12669226014483/100000000000000 : ℝ), (8733076996353/20000000000000 : ℝ), (10916347247623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2000941553/10000000000 : ℝ)|^4629 ≤ (12669226014483/100000000000000 : ℝ)^3605
        have hw : |(-2000941553/10000000000 : ℝ)|=(2000941553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244981889/10000000000 : ℝ)|^4629 ≤ (8733076996353/20000000000000 : ℝ)^3605
        have hw : |(5244981889/10000000000 : ℝ)|=(5244981889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655622783/1250000000 : ℝ)|^4629 ≤ (10916347247623/25000000000000 : ℝ)^3605
        have hw : |(655622783/1250000000 : ℝ)|=(655622783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_5 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688281173/5000000000 : ℝ)*x 0 + (-1825076619/10000000000 : ℝ)*x 1 + (5244982179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688281173/5000000000 : ℝ)^4629 ≤ (11269238483417/25000000000000 : ℝ)^3605 := by
    have hnat : (2688281173 : ℕ)^4629*25000000000000^3605 ≤ 11269238483417^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688281173 5000000000 11269238483417 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1825076619/10000000000 : ℝ)^4629 ≤ (5628828980939/50000000000000 : ℝ)^3605 := by
    have hnat : (1825076619 : ℕ)^4629*50000000000000^3605 ≤ 5628828980939^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1825076619 10000000000 5628828980939 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244982179/10000000000 : ℝ)^4629 ≤ (5458173510231/12500000000000 : ℝ)^3605 := by
    have hnat : (5244982179 : ℕ)^4629*12500000000000^3605 ≤ 5458173510231^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244982179 10000000000 5458173510231 12500000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688281173/5000000000 : ℝ), (-1825076619/10000000000 : ℝ), (5244982179/10000000000 : ℝ)] ![(11269238483417/25000000000000 : ℝ), (5628828980939/50000000000000 : ℝ), (5458173510231/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688281173/5000000000 : ℝ)|^4629 ≤ (11269238483417/25000000000000 : ℝ)^3605
        have hw : |(2688281173/5000000000 : ℝ)|=(2688281173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1825076619/10000000000 : ℝ)|^4629 ≤ (5628828980939/50000000000000 : ℝ)^3605
        have hw : |(-1825076619/10000000000 : ℝ)|=(1825076619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244982179/10000000000 : ℝ)|^4629 ≤ (5458173510231/12500000000000 : ℝ)^3605
        have hw : |(5244982179/10000000000 : ℝ)|=(5244982179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_6 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672070223/1250000000 : ℝ)*x 0 + (1048996551/2000000000 : ℝ)*x 1 + (-1825076607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672070223/1250000000 : ℝ)^4629 ≤ (4507694788349/10000000000000 : ℝ)^3605 := by
    have hnat : (672070223 : ℕ)^4629*10000000000000^3605 ≤ 4507694788349^3605*1250000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672070223 1250000000 4507694788349 10000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048996551/2000000000 : ℝ)^4629 ≤ (10916348559813/25000000000000 : ℝ)^3605 := by
    have hnat : (1048996551 : ℕ)^4629*25000000000000^3605 ≤ 10916348559813^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048996551 2000000000 10916348559813 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1825076607/10000000000 : ℝ)^4629 ≤ (11257657866833/100000000000000 : ℝ)^3605 := by
    have hnat : (1825076607 : ℕ)^4629*100000000000000^3605 ≤ 11257657866833^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1825076607 10000000000 11257657866833 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672070223/1250000000 : ℝ), (1048996551/2000000000 : ℝ), (-1825076607/10000000000 : ℝ)] ![(4507694788349/10000000000000 : ℝ), (10916348559813/25000000000000 : ℝ), (11257657866833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672070223/1250000000 : ℝ)|^4629 ≤ (4507694788349/10000000000000 : ℝ)^3605
        have hw : |(672070223/1250000000 : ℝ)|=(672070223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048996551/2000000000 : ℝ)|^4629 ≤ (10916348559813/25000000000000 : ℝ)^3605
        have hw : |(1048996551/2000000000 : ℝ)|=(1048996551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1825076607/10000000000 : ℝ)|^4629 ≤ (11257657866833/100000000000000 : ℝ)^3605
        have hw : |(-1825076607/10000000000 : ℝ)|=(1825076607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_7 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4041760277/10000000000 : ℝ)*x 0 + (4353555707/10000000000 : ℝ)*x 1 + (4353554803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4041760277/10000000000 : ℝ)^4629 ≤ (31247619934593/100000000000000 : ℝ)^3605 := by
    have hnat : (4041760277 : ℕ)^4629*100000000000000^3605 ≤ 31247619934593^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041760277 10000000000 31247619934593 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4353555707/10000000000 : ℝ)^4629 ≤ (34376194609291/100000000000000 : ℝ)^3605 := by
    have hnat : (4353555707 : ℕ)^4629*100000000000000^3605 ≤ 34376194609291^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353555707 10000000000 34376194609291 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4353554803/10000000000 : ℝ)^4629 ≤ (275009483549/800000000000 : ℝ)^3605 := by
    have hnat : (4353554803 : ℕ)^4629*800000000000^3605 ≤ 275009483549^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353554803 10000000000 275009483549 800000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4041760277/10000000000 : ℝ), (4353555707/10000000000 : ℝ), (4353554803/10000000000 : ℝ)] ![(31247619934593/100000000000000 : ℝ), (34376194609291/100000000000000 : ℝ), (275009483549/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4041760277/10000000000 : ℝ)|^4629 ≤ (31247619934593/100000000000000 : ℝ)^3605
        have hw : |(4041760277/10000000000 : ℝ)|=(4041760277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4353555707/10000000000 : ℝ)|^4629 ≤ (34376194609291/100000000000000 : ℝ)^3605
        have hw : |(4353555707/10000000000 : ℝ)|=(4353555707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4353554803/10000000000 : ℝ)|^4629 ≤ (275009483549/800000000000 : ℝ)^3605
        have hw : |(4353554803/10000000000 : ℝ)|=(4353554803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_8 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-478285121/2500000000 : ℝ)*x 0 + (5137904971/10000000000 : ℝ)*x 1 + (169290781/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (478285121/2500000000 : ℝ)^4629 ≤ (5979943933811/50000000000000 : ℝ)^3605 := by
    have hnat : (478285121 : ℕ)^4629*50000000000000^3605 ≤ 5979943933811^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478285121 2500000000 5979943933811 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137904971/10000000000 : ℝ)^4629 ≤ (21262037230807/50000000000000 : ℝ)^3605 := by
    have hnat : (5137904971 : ℕ)^4629*50000000000000^3605 ≤ 21262037230807^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137904971 10000000000 21262037230807 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169290781/312500000 : ℝ)^4629 ≤ (5689504705987/12500000000000 : ℝ)^3605 := by
    have hnat : (169290781 : ℕ)^4629*12500000000000^3605 ≤ 5689504705987^3605*312500000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169290781 312500000 5689504705987 12500000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-478285121/2500000000 : ℝ), (5137904971/10000000000 : ℝ), (169290781/312500000 : ℝ)] ![(5979943933811/50000000000000 : ℝ), (21262037230807/50000000000000 : ℝ), (5689504705987/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-478285121/2500000000 : ℝ)|^4629 ≤ (5979943933811/50000000000000 : ℝ)^3605
        have hw : |(-478285121/2500000000 : ℝ)|=(478285121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137904971/10000000000 : ℝ)|^4629 ≤ (21262037230807/50000000000000 : ℝ)^3605
        have hw : |(5137904971/10000000000 : ℝ)|=(5137904971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169290781/312500000 : ℝ)|^4629 ≤ (5689504705987/12500000000000 : ℝ)^3605
        have hw : |(169290781/312500000 : ℝ)|=(169290781/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_9 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257072539/10000000000 : ℝ)*x 0 + (-1752906837/10000000000 : ℝ)*x 1 + (5417305319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257072539/10000000000 : ℝ)^4629 ≤ (43794675580203/100000000000000 : ℝ)^3605 := by
    have hnat : (5257072539 : ℕ)^4629*100000000000000^3605 ≤ 43794675580203^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257072539 10000000000 43794675580203 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1752906837/10000000000 : ℝ)^4629 ≤ (10689283227351/100000000000000 : ℝ)^3605 := by
    have hnat : (1752906837 : ℕ)^4629*100000000000000^3605 ≤ 10689283227351^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752906837 10000000000 10689283227351 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417305319/10000000000 : ℝ)^4629 ≤ (5689505146969/12500000000000 : ℝ)^3605 := by
    have hnat : (5417305319 : ℕ)^4629*12500000000000^3605 ≤ 5689505146969^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417305319 10000000000 5689505146969 12500000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257072539/10000000000 : ℝ), (-1752906837/10000000000 : ℝ), (5417305319/10000000000 : ℝ)] ![(43794675580203/100000000000000 : ℝ), (10689283227351/100000000000000 : ℝ), (5689505146969/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257072539/10000000000 : ℝ)|^4629 ≤ (43794675580203/100000000000000 : ℝ)^3605
        have hw : |(5257072539/10000000000 : ℝ)|=(5257072539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1752906837/10000000000 : ℝ)|^4629 ≤ (10689283227351/100000000000000 : ℝ)^3605
        have hw : |(-1752906837/10000000000 : ℝ)|=(1752906837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417305319/10000000000 : ℝ)|^4629 ≤ (5689505146969/12500000000000 : ℝ)^3605
        have hw : |(5417305319/10000000000 : ℝ)|=(5417305319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_10 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257072449/10000000000 : ℝ)*x 0 + (1083461279/2000000000 : ℝ)*x 1 + (-876452739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257072449/10000000000 : ℝ)^4629 ≤ (43794674617479/100000000000000 : ℝ)^3605 := by
    have hnat : (5257072449 : ℕ)^4629*100000000000000^3605 ≤ 43794674617479^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257072449 10000000000 43794674617479 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083461279/2000000000 : ℝ)^4629 ≤ (5689506598029/12500000000000 : ℝ)^3605 := by
    have hnat : (1083461279 : ℕ)^4629*12500000000000^3605 ≤ 5689506598029^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083461279 2000000000 5689506598029 12500000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (876452739/5000000000 : ℝ)^4629 ≤ (534463629307/5000000000000 : ℝ)^3605 := by
    have hnat : (876452739 : ℕ)^4629*5000000000000^3605 ≤ 534463629307^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876452739 5000000000 534463629307 5000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257072449/10000000000 : ℝ), (1083461279/2000000000 : ℝ), (-876452739/5000000000 : ℝ)] ![(43794674617479/100000000000000 : ℝ), (5689506598029/12500000000000 : ℝ), (534463629307/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257072449/10000000000 : ℝ)|^4629 ≤ (43794674617479/100000000000000 : ℝ)^3605
        have hw : |(5257072449/10000000000 : ℝ)|=(5257072449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083461279/2000000000 : ℝ)|^4629 ≤ (5689506598029/12500000000000 : ℝ)^3605
        have hw : |(1083461279/2000000000 : ℝ)|=(1083461279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-876452739/5000000000 : ℝ)|^4629 ≤ (534463629307/5000000000000 : ℝ)^3605
        have hw : |(-876452739/5000000000 : ℝ)|=(876452739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_11 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (44989091/100000000 : ℝ)*x 0 + (1031129897/2500000000 : ℝ)*x 1 + (2062259541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44989091/100000000 : ℝ)^4629 ≤ (35856867618183/100000000000000 : ℝ)^3605 := by
    have hnat : (44989091 : ℕ)^4629*100000000000000^3605 ≤ 35856867618183^3605*100000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44989091 100000000 35856867618183 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031129897/2500000000 : ℝ)^4629 ≤ (8017892178089/25000000000000 : ℝ)^3605 := by
    have hnat : (1031129897 : ℕ)^4629*25000000000000^3605 ≤ 8017892178089^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031129897 2500000000 8017892178089 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2062259541/5000000000 : ℝ)^4629 ≤ (32071563660171/100000000000000 : ℝ)^3605 := by
    have hnat : (2062259541 : ℕ)^4629*100000000000000^3605 ≤ 32071563660171^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062259541 5000000000 32071563660171 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44989091/100000000 : ℝ), (1031129897/2500000000 : ℝ), (2062259541/5000000000 : ℝ)] ![(35856867618183/100000000000000 : ℝ), (8017892178089/25000000000000 : ℝ), (32071563660171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44989091/100000000 : ℝ)|^4629 ≤ (35856867618183/100000000000000 : ℝ)^3605
        have hw : |(44989091/100000000 : ℝ)|=(44989091/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031129897/2500000000 : ℝ)|^4629 ≤ (8017892178089/25000000000000 : ℝ)^3605
        have hw : |(1031129897/2500000000 : ℝ)|=(1031129897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2062259541/5000000000 : ℝ)|^4629 ≤ (32071563660171/100000000000000 : ℝ)^3605
        have hw : |(2062259541/5000000000 : ℝ)|=(2062259541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_12 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1674122809/10000000000 : ℝ)*x 0 + (5500824251/10000000000 : ℝ)*x 1 + (209197301/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1674122809/10000000000 : ℝ)^4629 ≤ (5038185550511/50000000000000 : ℝ)^3605 := by
    have hnat : (1674122809 : ℕ)^4629*50000000000000^3605 ≤ 5038185550511^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674122809 10000000000 5038185550511 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5500824251/10000000000 : ℝ)^4629 ≤ (23209527541767/50000000000000 : ℝ)^3605 := by
    have hnat : (5500824251 : ℕ)^4629*50000000000000^3605 ≤ 23209527541767^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500824251 10000000000 23209527541767 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209197301/400000000 : ℝ)^4629 ≤ (21752286903987/50000000000000 : ℝ)^3605 := by
    have hnat : (209197301 : ℕ)^4629*50000000000000^3605 ≤ 21752286903987^3605*400000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209197301 400000000 21752286903987 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1674122809/10000000000 : ℝ), (5500824251/10000000000 : ℝ), (209197301/400000000 : ℝ)] ![(5038185550511/50000000000000 : ℝ), (23209527541767/50000000000000 : ℝ), (21752286903987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1674122809/10000000000 : ℝ)|^4629 ≤ (5038185550511/50000000000000 : ℝ)^3605
        have hw : |(-1674122809/10000000000 : ℝ)|=(1674122809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5500824251/10000000000 : ℝ)|^4629 ≤ (23209527541767/50000000000000 : ℝ)^3605
        have hw : |(5500824251/10000000000 : ℝ)|=(5500824251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209197301/400000000 : ℝ)|^4629 ≤ (21752286903987/50000000000000 : ℝ)^3605
        have hw : |(209197301/400000000 : ℝ)|=(209197301/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_13 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2693499261/5000000000 : ℝ)*x 0 + (-915594309/5000000000 : ℝ)*x 1 + (5229932583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2693499261/5000000000 : ℝ)^4629 ≤ (45189334918717/100000000000000 : ℝ)^3605 := by
    have hnat : (2693499261 : ℕ)^4629*100000000000000^3605 ≤ 45189334918717^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693499261 5000000000 45189334918717 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (915594309/5000000000 : ℝ)^4629 ≤ (5653045319913/50000000000000 : ℝ)^3605 := by
    have hnat : (915594309 : ℕ)^4629*50000000000000^3605 ≤ 5653045319913^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915594309 5000000000 5653045319913 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229932583/10000000000 : ℝ)^4629 ≤ (8700914885497/20000000000000 : ℝ)^3605 := by
    have hnat : (5229932583 : ℕ)^4629*20000000000000^3605 ≤ 8700914885497^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229932583 10000000000 8700914885497 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2693499261/5000000000 : ℝ), (-915594309/5000000000 : ℝ), (5229932583/10000000000 : ℝ)] ![(45189334918717/100000000000000 : ℝ), (5653045319913/50000000000000 : ℝ), (8700914885497/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2693499261/5000000000 : ℝ)|^4629 ≤ (45189334918717/100000000000000 : ℝ)^3605
        have hw : |(2693499261/5000000000 : ℝ)|=(2693499261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-915594309/5000000000 : ℝ)|^4629 ≤ (5653045319913/50000000000000 : ℝ)^3605
        have hw : |(-915594309/5000000000 : ℝ)|=(915594309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229932583/10000000000 : ℝ)|^4629 ≤ (8700914885497/20000000000000 : ℝ)^3605
        have hw : |(5229932583/10000000000 : ℝ)|=(5229932583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_14 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346749503/2500000000 : ℝ)*x 0 + (2614966537/5000000000 : ℝ)*x 1 + (-36623773/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346749503/2500000000 : ℝ)^4629 ≤ (22594664712659/50000000000000 : ℝ)^3605 := by
    have hnat : (1346749503 : ℕ)^4629*50000000000000^3605 ≤ 22594664712659^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346749503 2500000000 22594664712659 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614966537/5000000000 : ℝ)^4629 ≤ (43504579671963/100000000000000 : ℝ)^3605 := by
    have hnat : (2614966537 : ℕ)^4629*100000000000000^3605 ≤ 43504579671963^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614966537 5000000000 43504579671963 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36623773/200000000 : ℝ)^4629 ≤ (141326136169/1250000000000 : ℝ)^3605 := by
    have hnat : (36623773 : ℕ)^4629*1250000000000^3605 ≤ 141326136169^3605*200000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36623773 200000000 141326136169 1250000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346749503/2500000000 : ℝ), (2614966537/5000000000 : ℝ), (-36623773/200000000 : ℝ)] ![(22594664712659/50000000000000 : ℝ), (43504579671963/100000000000000 : ℝ), (141326136169/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346749503/2500000000 : ℝ)|^4629 ≤ (22594664712659/50000000000000 : ℝ)^3605
        have hw : |(1346749503/2500000000 : ℝ)|=(1346749503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614966537/5000000000 : ℝ)|^4629 ≤ (43504579671963/100000000000000 : ℝ)^3605
        have hw : |(2614966537/5000000000 : ℝ)|=(2614966537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-36623773/200000000 : ℝ)|^4629 ≤ (141326136169/1250000000000 : ℝ)^3605
        have hw : |(-36623773/200000000 : ℝ)|=(36623773/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_box_15 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4000871677/10000000000 : ℝ)*x 0 + (874706119/2000000000 : ℝ)*x 1 + (2186765399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4000871677/10000000000 : ℝ)^4629 ≤ (3084229381913/10000000000000 : ℝ)^3605 := by
    have hnat : (4000871677 : ℕ)^4629*10000000000000^3605 ≤ 3084229381913^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4000871677 10000000000 3084229381913 10000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (874706119/2000000000 : ℝ)^4629 ≤ (34578852052221/100000000000000 : ℝ)^3605 := by
    have hnat : (874706119 : ℕ)^4629*100000000000000^3605 ≤ 34578852052221^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874706119 2000000000 34578852052221 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2186765399/5000000000 : ℝ)^4629 ≤ (17289427056559/50000000000000 : ℝ)^3605 := by
    have hnat : (2186765399 : ℕ)^4629*50000000000000^3605 ≤ 17289427056559^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186765399 5000000000 17289427056559 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4000871677/10000000000 : ℝ), (874706119/2000000000 : ℝ), (2186765399/5000000000 : ℝ)] ![(3084229381913/10000000000000 : ℝ), (34578852052221/100000000000000 : ℝ), (17289427056559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4000871677/10000000000 : ℝ)|^4629 ≤ (3084229381913/10000000000000 : ℝ)^3605
        have hw : |(4000871677/10000000000 : ℝ)|=(4000871677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(874706119/2000000000 : ℝ)|^4629 ≤ (34578852052221/100000000000000 : ℝ)^3605
        have hw : |(874706119/2000000000 : ℝ)|=(874706119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2186765399/5000000000 : ℝ)|^4629 ≤ (17289427056559/50000000000000 : ℝ)^3605
        have hw : |(2186765399/5000000000 : ℝ)|=(2186765399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1566_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2777/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31911/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58883/100000 : ℝ) ∧ (1011/1250 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43171/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2777/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2777/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2777/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2777/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2777/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2777/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2777/25000 : ℝ) ^ (4627/1024 : ℝ) ≤ (1217849158429667/25000000000000000000 : ℝ) := by
    have hpowers : (2777/25000 : ℝ)^4627 ≤ (1217849158429667/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2777 : ℕ)^4627*25000000000000000000^1024 ≤ 1217849158429667^1024*25000^4627 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2777 25000 1217849158429667 25000000000000000000 4627 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2777/25000 : ℝ)) (X := (1217849158429667/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4627/1024 : ℝ) ≤ (4371188095715341/20000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4627 ≤ (4371188095715341/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4627*20000000000000000000^1024 ≤ 4371188095715341^1024*20000^4627 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 4371188095715341 20000000000000000000 4627 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (4371188095715341/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501217849158429667/12500000000000000000 : ℝ) ≤ (2000043121858153/2000000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (12501217849158429667/12500000000000000000 : ℝ)^1024 ≤ (2000043121858153/2000000000000000 : ℝ)^4627 := by
      have hnat : (12501217849158429667 : ℕ)^1024*2000000000000000^4627 ≤ 2000043121858153^4627*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501217849158429667 12500000000000000000 2000043121858153 2000000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000043121858153/2000000000000000 : ℝ)) (X := (12501217849158429667/12500000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026727337112295373/100000000000000000000 : ℝ) ≤ (10000591440363391/10000000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (100026727337112295373/100000000000000000000 : ℝ)^1024 ≤ (10000591440363391/10000000000000000 : ℝ)^4627 := by
      have hnat : (100026727337112295373 : ℕ)^1024*10000000000000000^4627 ≤ 10000591440363391^4627*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026727337112295373 100000000000000000000 10000591440363391 10000000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000591440363391/10000000000000000 : ℝ)) (X := (100026727337112295373/100000000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004371188095715341/10000000000000000000 : ℝ) ≤ (10000967271436017/10000000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (10004371188095715341/10000000000000000000 : ℝ)^1024 ≤ (10000967271436017/10000000000000000 : ℝ)^4627 := by
      have hnat : (10004371188095715341 : ℕ)^1024*10000000000000000^4627 ≤ 10000967271436017^4627*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004371188095715341 10000000000000000000 10000967271436017 10000000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000967271436017/10000000000000000 : ℝ)) (X := (10004371188095715341/10000000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1217849158429667/25000000000000000000 : ℝ) ≤ ((43762594258756219189/43770000000000000000 : ℝ)+2*(187915536313/218850000000000 : ℝ)*(2777/25000 : ℝ))^(4627/1024 : ℝ) := by
    rw [show (43762594258756219189/43770000000000000000 : ℝ)+2*(187915536313/218850000000000 : ℝ)*(2777/25000 : ℝ)=(2000043121858153/2000000000000000 : ℝ) by norm_num, show 1+2*(1217849158429667/25000000000000000000 : ℝ)=(12501217849158429667/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4371188095715341/20000000000000000000 : ℝ)+(1217849158429667/25000000000000000000 : ℝ) ≤ ((43762594258756219189/43770000000000000000 : ℝ)+(187915536313/218850000000000 : ℝ)*((3097/20000 : ℝ)+(2777/25000 : ℝ)))^(4627/1024 : ℝ) := by
    rw [show (43762594258756219189/43770000000000000000 : ℝ)+(187915536313/218850000000000 : ℝ)*((3097/20000 : ℝ)+(2777/25000 : ℝ))=(10000591440363391/10000000000000000 : ℝ) by norm_num, show 1+(4371188095715341/20000000000000000000 : ℝ)+(1217849158429667/25000000000000000000 : ℝ)=(100026727337112295373/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4371188095715341/20000000000000000000 : ℝ) ≤ ((43762594258756219189/43770000000000000000 : ℝ)+2*(187915536313/218850000000000 : ℝ)*(3097/20000 : ℝ))^(4627/1024 : ℝ) := by
    rw [show (43762594258756219189/43770000000000000000 : ℝ)+2*(187915536313/218850000000000 : ℝ)*(3097/20000 : ℝ)=(10000967271436017/10000000000000000 : ℝ) by norm_num, show 1+2*(4371188095715341/20000000000000000000 : ℝ)=(10004371188095715341/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43762594258756219189/43770000000000000000 : ℝ)*(X 1 0+X 2 0)+(187915536313/218850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (2777/25000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (43762594258756219189/43770000000000000000 : ℝ)) (alpha := (187915536313/218850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43762594258756219189/43770000000000000000 : ℝ)*(X 0 1+X 2 1)+(187915536313/218850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (2777/25000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (43762594258756219189/43770000000000000000 : ℝ)) (alpha := (187915536313/218850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43762594258756219189/43770000000000000000 : ℝ)*(X 0 2+X 1 2)+(187915536313/218850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (2777/25000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (43762594258756219189/43770000000000000000 : ℝ)) (alpha := (187915536313/218850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1586641677/10000000000 : ℝ)*X 0 0+(134925549/250000000 : ℝ)*X 0 1+(134925529/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1054228091/2000000000 : ℝ)*X 1 0+(-880803649/5000000000 : ℝ)*X 1 1+(5397021657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271141027/10000000000 : ℝ)*X 2 0+(2698510761/5000000000 : ℝ)*X 2 1+(-1761606701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1111527371/2500000000 : ℝ)*X 0 0+(830301597/2000000000 : ℝ)*X 0 1+(83030181/200000000 : ℝ)*X 0 2+(1111527371/2500000000 : ℝ)*X 1 0+(830301597/2000000000 : ℝ)*X 1 1+(83030181/200000000 : ℝ)*X 1 2+(1111527371/2500000000 : ℝ)*X 2 0+(830301597/2000000000 : ℝ)*X 2 1+(83030181/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2000941553/10000000000 : ℝ)*X 0 0+(5244981889/10000000000 : ℝ)*X 0 1+(655622783/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2688281173/5000000000 : ℝ)*X 1 0+(-1825076619/10000000000 : ℝ)*X 1 1+(5244982179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((672070223/1250000000 : ℝ)*X 2 0+(1048996551/2000000000 : ℝ)*X 2 1+(-1825076607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4041760277/10000000000 : ℝ)*X 0 0+(4353555707/10000000000 : ℝ)*X 0 1+(4353554803/10000000000 : ℝ)*X 0 2+(4041760277/10000000000 : ℝ)*X 1 0+(4353555707/10000000000 : ℝ)*X 1 1+(4353554803/10000000000 : ℝ)*X 1 2+(4041760277/10000000000 : ℝ)*X 2 0+(4353555707/10000000000 : ℝ)*X 2 1+(4353554803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-478285121/2500000000 : ℝ)*X 0 0+(5137904971/10000000000 : ℝ)*X 0 1+(169290781/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5257072539/10000000000 : ℝ)*X 1 0+(-1752906837/10000000000 : ℝ)*X 1 1+(5417305319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5257072449/10000000000 : ℝ)*X 2 0+(1083461279/2000000000 : ℝ)*X 2 1+(-876452739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((44989091/100000000 : ℝ)*X 0 0+(1031129897/2500000000 : ℝ)*X 0 1+(2062259541/5000000000 : ℝ)*X 0 2+(44989091/100000000 : ℝ)*X 1 0+(1031129897/2500000000 : ℝ)*X 1 1+(2062259541/5000000000 : ℝ)*X 1 2+(44989091/100000000 : ℝ)*X 2 0+(1031129897/2500000000 : ℝ)*X 2 1+(2062259541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1674122809/10000000000 : ℝ)*X 0 0+(5500824251/10000000000 : ℝ)*X 0 1+(209197301/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2693499261/5000000000 : ℝ)*X 1 0+(-915594309/5000000000 : ℝ)*X 1 1+(5229932583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1346749503/2500000000 : ℝ)*X 2 0+(2614966537/5000000000 : ℝ)*X 2 1+(-36623773/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4000871677/10000000000 : ℝ)*X 0 0+(874706119/2000000000 : ℝ)*X 0 1+(2186765399/5000000000 : ℝ)*X 0 2+(4000871677/10000000000 : ℝ)*X 1 0+(874706119/2000000000 : ℝ)*X 1 1+(2186765399/5000000000 : ℝ)*X 1 2+(4000871677/10000000000 : ℝ)*X 2 0+(874706119/2000000000 : ℝ)*X 2 1+(2186765399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31911/50000 : ℝ) ≤ (-93112215043453255904256969/145900000000000000000000000 : ℝ) := by norm_num
    linear_combination (5027493/3125000000000 : ℝ)*(lower0) + (1165863/10000000000000 : ℝ)*(upper1) + (23424473/25000000000000 : ℝ)*(lower4) + (230198449638393/10000000000000 : ℝ)*(major0) + (230198449638393/10000000000000 : ℝ)*(major1) + (230198449638393/10000000000000 : ℝ)*(major2) + (6383057/625000000000 : ℝ)*(sp1) + (813153818990409/25000000000000 : ℝ)*(sp4) + (1626307280487027/50000000000000 : ℝ)*(sp5) + (3252540524032689/100000000000000 : ℝ)*(sp6) + (1372609726056473/100000000000000 : ℝ)*(sp7) + (306301537/100000000000000 : ℝ)*(sp12) + (15011646097/20000000000000 : ℝ)*(sp14) + (16751627431/100000000000000 : ℝ)*(sp15) + (21447288713811/1562500000000 : ℝ)*(f.failure) + (1626307791131587/50000000000000 : ℝ)*(f.sum) + (2390656737141/1459000000000000000000000000 : ℝ)*base66 + (941030198809207759/145900000000000000000000000000000 : ℝ)*base67 + (487259672869107759/145900000000000000000000000000000 : ℝ)*base69 + (375372691956292241/145900000000000000000000000000000 : ℝ)*base72 + (777744333259/729500000000000000000000000 : ℝ)*base74 + (42596701905192241/145900000000000000000000000000000 : ℝ)*base76 + (327843244637092241/145900000000000000000000000000000 : ℝ)*base78 + (131160469774607759/145900000000000000000000000000000 : ℝ)*base79 + (536311979207/182375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (823239/156250000000000000000 : ℝ)*base89 + (823239/156250000000000000000 : ℝ)*base91 + (823239/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58883/100000 : ℝ) ≤ (107393108361682972908340850922051/182375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (539957/25000000000000 : ℝ)*(upper0) + (288173137/100000000000000 : ℝ)*(lower1) + (286198579/100000000000000 : ℝ)*(upper4) + (595486653310841/25000000000000 : ℝ)*(major0) + (595486653310841/25000000000000 : ℝ)*(major1) + (595486653310841/25000000000000 : ℝ)*(major2) + (664790530642301/20000000000000 : ℝ)*(sp0) + (207743251676863/6250000000000 : ℝ)*(sp1) + (830989519936959/25000000000000 : ℝ)*(sp2) + (71015049582409/5000000000000 : ℝ)*(sp3) + (65811081/25000000000000 : ℝ)*(sp6) + (1053594803/20000000000000 : ℝ)*(sp7) + (1137956131/20000000000000 : ℝ)*(sp8) + (66316162353/100000000000000 : ℝ)*(sp9) + (284061251924439/20000000000000 : ℝ)*(f.failure) + (20774739643701/625000000000 : ℝ)*(f.sum) + (31373703053207/10942500000000000000000000000 : ℝ)*base65 + (3481528145091675983/364750000000000000000000000000000 : ℝ)*base67 + (1220628226390425983/364750000000000000000000000000000 : ℝ)*base69 + (140910419320324017/364750000000000000000000000000000 : ℝ)*base72 + (31749816217441/5471250000000000000000000000 : ℝ)*base73 + (1495419239771175983/364750000000000000000000000000000 : ℝ)*base75 + (1953931015784925983/364750000000000000000000000000000 : ℝ)*base77 + (1888603382161574017/364750000000000000000000000000000 : ℝ)*base80 + (134364209016079/21885000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (6548989/2000000000000000000000 : ℝ)*base90 + (6548989/2000000000000000000000 : ℝ)*base92 + (6548989/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (1011/1250 : ℝ) ≤ (147509371180000772674574860426069/182375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (314810443/100000000000000 : ℝ)*(lower3) + (169415221/50000000000000 : ℝ)*(upper4) + (135381467/100000000000000 : ℝ)*(lower5) + (642239416327921/25000000000000 : ℝ)*(major0) + (642239416327921/25000000000000 : ℝ)*(major1) + (642239416327921/25000000000000 : ℝ)*(major2) + (5557405483/20000000000000 : ℝ)*(sp0) + (240691732323/100000000000000 : ℝ)*(sp1) + (100883797233/20000000000000 : ℝ)*(sp2) + (34959243977/20000000000000 : ℝ)*(sp3) + (894777396174133/25000000000000 : ℝ)*(sp8) + (447362084998953/12500000000000 : ℝ)*(sp9) + (1789316476368891/50000000000000 : ℝ)*(sp10) + (382910586366477/25000000000000 : ℝ)*(sp11) + (765908570842897/50000000000000 : ℝ)*(f.failure) + (894784342930987/25000000000000 : ℝ)*(f.sum) + (35156797266661/21885000000000000000000000000 : ℝ)*base66 + (2880902831312342023/364750000000000000000000000000000 : ℝ)*base67 + (3709876239592023/364750000000000000000000000000000 : ℝ)*base69 + (2294721247577657977/364750000000000000000000000000000 : ℝ)*base72 + (245645580473189/21885000000000000000000000000 : ℝ)*base73 + (647287944124657977/364750000000000000000000000000000 : ℝ)*base76 + (789623877039657977/364750000000000000000000000000000 : ℝ)*base78 + (17278494945657977/364750000000000000000000000000000 : ℝ)*base80 + (127808136210359/21885000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (77032453/5000000000000000000000 : ℝ)*base89 + (77032453/5000000000000000000000 : ℝ)*base91 + (77032453/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-43171/50000 : ℝ) ≤ (-314922398907581397006667470608447/364750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47912499/100000000000000 : ℝ)*(upper3) + (19108677/20000000000000 : ℝ)*(lower4) + (13373373/100000000000000 : ℝ)*(upper5) + (1304656957323923/50000000000000 : ℝ)*(major0) + (1304656957323923/50000000000000 : ℝ)*(major1) + (1304656957323923/50000000000000 : ℝ)*(major2) + (229631407/50000000000000 : ℝ)*(sp4) + (88849098381/100000000000000 : ℝ)*(sp5) + (2189167407/4000000000000 : ℝ)*(sp7) + (284250627/5000000000000 : ℝ)*(sp8) + (1845760341127367/50000000000000 : ℝ)*(sp12) + (922859494357927/25000000000000 : ℝ)*(sp13) + (3691526826530089/100000000000000 : ℝ)*(sp14) + (777913011083453/50000000000000 : ℝ)*(sp15) + (1555880751352081/100000000000000 : ℝ)*(f.failure) + (3691526826530089/100000000000000 : ℝ)*(f.sum) + (49463022308569/21885000000000000000000000000 : ℝ)*base66 + (5338653155837886149/729500000000000000000000000000000 : ℝ)*base67 + (1084865297970113851/729500000000000000000000000000000 : ℝ)*base70 + (2439431391070113851/729500000000000000000000000000000 : ℝ)*base72 + (16309507878997/2735625000000000000000000000 : ℝ)*base73 + (1294661545038386149/729500000000000000000000000000000 : ℝ)*base75 + (29863615582886149/729500000000000000000000000000000 : ℝ)*base77 + (1117768077340886149/729500000000000000000000000000000 : ℝ)*base79 + (53619402556159/21885000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (11521531/10000000000000000000000 : ℝ)*base90 + (11521531/10000000000000000000000 : ℝ)*base92 + (11521531/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1566_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2777/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31911/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58883/100000 : ℝ) else (1011/1250 : ℝ) ≤ X j i ∧ X j i ≤ (43171/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1566_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1566_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2777/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31911/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58883/100000 : ℝ) else (1011/1250 : ℝ) ≤ X j i ∧ X j i ≤ (43171/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1566_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2777/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31911/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58883/100000 : ℝ) else (1011/1250 : ℝ) ≤ X j i ∧ X j i ≤ (43171/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1566_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
