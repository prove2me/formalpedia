-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1748_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:18:31.593307+00:00
-- url     : https://prove2.me/submissions/578a0cf4-34e1-4fb5-a0c4-642c2393a407

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
theorem support_rectangle_w1748_s3_0 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-154175171/1250000000 : ℝ)*x 0 + (5499724001/10000000000 : ℝ)*x 1 + (101610623/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (154175171/1250000000 : ℝ)^5743 ≤ (1566421053779/20000000000000 : ℝ)^4719 := by
    have hnat : (154175171 : ℕ)^5743*20000000000000^4719 ≤ 1566421053779^4719*1250000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154175171 1250000000 1566421053779 20000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5499724001/10000000000 : ℝ)^5743 ≤ (9661090065729/20000000000000 : ℝ)^4719 := by
    have hnat : (5499724001 : ℕ)^5743*20000000000000^4719 ≤ 9661090065729^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499724001 10000000000 9661090065729 20000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101610623/200000000 : ℝ)^5743 ≤ (43862444384489/100000000000000 : ℝ)^4719 := by
    have hnat : (101610623 : ℕ)^5743*100000000000000^4719 ≤ 43862444384489^4719*200000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101610623 200000000 43862444384489 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-154175171/1250000000 : ℝ), (5499724001/10000000000 : ℝ), (101610623/200000000 : ℝ)] ![(1566421053779/20000000000000 : ℝ), (9661090065729/20000000000000 : ℝ), (43862444384489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-154175171/1250000000 : ℝ)|^5743 ≤ (1566421053779/20000000000000 : ℝ)^4719
        have hw : |(-154175171/1250000000 : ℝ)|=(154175171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5499724001/10000000000 : ℝ)|^5743 ≤ (9661090065729/20000000000000 : ℝ)^4719
        have hw : |(5499724001/10000000000 : ℝ)|=(5499724001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(101610623/200000000 : ℝ)|^5743 ≤ (43862444384489/100000000000000 : ℝ)^4719
        have hw : |(101610623/200000000 : ℝ)|=(101610623/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s3_1 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5337682617/10000000000 : ℝ)*x 0 + (-1452761473/10000000000 : ℝ)*x 1 + (635066481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5337682617/10000000000 : ℝ)^5743 ≤ (23289471102803/50000000000000 : ℝ)^4719 := by
    have hnat : (5337682617 : ℕ)^5743*50000000000000^4719 ≤ 23289471102803^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5337682617 10000000000 23289471102803 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1452761473/10000000000 : ℝ)^5743 ≤ (9558606061701/100000000000000 : ℝ)^4719 := by
    have hnat : (1452761473 : ℕ)^5743*100000000000000^4719 ≤ 9558606061701^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1452761473 10000000000 9558606061701 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635066481/1250000000 : ℝ)^5743 ≤ (43862451718271/100000000000000 : ℝ)^4719 := by
    have hnat : (635066481 : ℕ)^5743*100000000000000^4719 ≤ 43862451718271^4719*1250000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635066481 1250000000 43862451718271 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5337682617/10000000000 : ℝ), (-1452761473/10000000000 : ℝ), (635066481/1250000000 : ℝ)] ![(23289471102803/50000000000000 : ℝ), (9558606061701/100000000000000 : ℝ), (43862451718271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5337682617/10000000000 : ℝ)|^5743 ≤ (23289471102803/50000000000000 : ℝ)^4719
        have hw : |(5337682617/10000000000 : ℝ)|=(5337682617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1452761473/10000000000 : ℝ)|^5743 ≤ (9558606061701/100000000000000 : ℝ)^4719
        have hw : |(-1452761473/10000000000 : ℝ)|=(1452761473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(635066481/1250000000 : ℝ)|^5743 ≤ (43862451718271/100000000000000 : ℝ)^4719
        have hw : |(635066481/1250000000 : ℝ)|=(635066481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s3_2 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5337682407/10000000000 : ℝ)*x 0 + (5080531971/10000000000 : ℝ)*x 1 + (-145276159/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5337682407/10000000000 : ℝ)^5743 ≤ (232894699877/500000000000 : ℝ)^4719 := by
    have hnat : (5337682407 : ℕ)^5743*500000000000^4719 ≤ 232894699877^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5337682407 10000000000 232894699877 500000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5080531971/10000000000 : ℝ)^5743 ≤ (21931226505307/50000000000000 : ℝ)^4719 := by
    have hnat : (5080531971 : ℕ)^5743*50000000000000^4719 ≤ 21931226505307^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080531971 10000000000 21931226505307 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145276159/1000000000 : ℝ)^5743 ≤ (4779303499281/50000000000000 : ℝ)^4719 := by
    have hnat : (145276159 : ℕ)^5743*50000000000000^4719 ≤ 4779303499281^4719*1000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145276159 1000000000 4779303499281 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5337682407/10000000000 : ℝ), (5080531971/10000000000 : ℝ), (-145276159/1000000000 : ℝ)] ![(232894699877/500000000000 : ℝ), (21931226505307/50000000000000 : ℝ), (4779303499281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5337682407/10000000000 : ℝ)|^5743 ≤ (232894699877/500000000000 : ℝ)^4719
        have hw : |(5337682407/10000000000 : ℝ)|=(5337682407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5080531971/10000000000 : ℝ)|^5743 ≤ (21931226505307/50000000000000 : ℝ)^4719
        have hw : |(5080531971/10000000000 : ℝ)|=(5080531971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-145276159/1000000000 : ℝ)|^5743 ≤ (4779303499281/50000000000000 : ℝ)^4719
        have hw : |(-145276159/1000000000 : ℝ)|=(145276159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s3_3 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (402506343/1000000000 : ℝ)*x 0 + (1686928749/5000000000 : ℝ)*x 1 + (1184977503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402506343/1000000000 : ℝ)^5743 ≤ (33037740462701/100000000000000 : ℝ)^4719 := by
    have hnat : (402506343 : ℕ)^5743*100000000000000^4719 ≤ 33037740462701^4719*1000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402506343 1000000000 33037740462701 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1686928749/5000000000 : ℝ)^5743 ≤ (26652167667127/100000000000000 : ℝ)^4719 := by
    have hnat : (1686928749 : ℕ)^5743*100000000000000^4719 ≤ 26652167667127^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686928749 5000000000 26652167667127 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1184977503/2500000000 : ℝ)^5743 ≤ (8062018371791/20000000000000 : ℝ)^4719 := by
    have hnat : (1184977503 : ℕ)^5743*20000000000000^4719 ≤ 8062018371791^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184977503 2500000000 8062018371791 20000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(402506343/1000000000 : ℝ), (1686928749/5000000000 : ℝ), (1184977503/2500000000 : ℝ)] ![(33037740462701/100000000000000 : ℝ), (26652167667127/100000000000000 : ℝ), (8062018371791/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(402506343/1000000000 : ℝ)|^5743 ≤ (33037740462701/100000000000000 : ℝ)^4719
        have hw : |(402506343/1000000000 : ℝ)|=(402506343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1686928749/5000000000 : ℝ)|^5743 ≤ (26652167667127/100000000000000 : ℝ)^4719
        have hw : |(1686928749/5000000000 : ℝ)|=(1686928749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1184977503/2500000000 : ℝ)|^5743 ≤ (8062018371791/20000000000000 : ℝ)^4719
        have hw : |(1184977503/2500000000 : ℝ)|=(1184977503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s3_4 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-246751223/2000000000 : ℝ)*x 0 + (2543663633/5000000000 : ℝ)*x 1 + (5492785407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246751223/2000000000 : ℝ)^5743 ≤ (7834846812841/100000000000000 : ℝ)^4719 := by
    have hnat : (246751223 : ℕ)^5743*100000000000000^4719 ≤ 7834846812841^4719*2000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246751223 2000000000 7834846812841 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2543663633/5000000000 : ℝ)^5743 ≤ (43933860518837/100000000000000 : ℝ)^4719 := by
    have hnat : (2543663633 : ℕ)^5743*100000000000000^4719 ≤ 43933860518837^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543663633 5000000000 43933860518837 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5492785407/10000000000 : ℝ)^5743 ≤ (6028911582167/12500000000000 : ℝ)^4719 := by
    have hnat : (5492785407 : ℕ)^5743*12500000000000^4719 ≤ 6028911582167^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492785407 10000000000 6028911582167 12500000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-246751223/2000000000 : ℝ), (2543663633/5000000000 : ℝ), (5492785407/10000000000 : ℝ)] ![(7834846812841/100000000000000 : ℝ), (43933860518837/100000000000000 : ℝ), (6028911582167/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-246751223/2000000000 : ℝ)|^5743 ≤ (7834846812841/100000000000000 : ℝ)^4719
        have hw : |(-246751223/2000000000 : ℝ)|=(246751223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2543663633/5000000000 : ℝ)|^5743 ≤ (43933860518837/100000000000000 : ℝ)^4719
        have hw : |(2543663633/5000000000 : ℝ)|=(2543663633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5492785407/10000000000 : ℝ)|^5743 ≤ (6028911582167/12500000000000 : ℝ)^4719
        have hw : |(5492785407/10000000000 : ℝ)|=(5492785407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s3_5 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613250021/5000000000 : ℝ)*x 0 + (-208101589/2000000000 : ℝ)*x 1 + (5492785387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613250021/5000000000 : ℝ)^5743 ≤ (45400863143361/100000000000000 : ℝ)^4719 := by
    have hnat : (2613250021 : ℕ)^5743*100000000000000^4719 ≤ 45400863143361^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613250021 5000000000 45400863143361 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208101589/2000000000 : ℝ)^5743 ≤ (6367844396439/100000000000000 : ℝ)^4719 := by
    have hnat : (208101589 : ℕ)^5743*100000000000000^4719 ≤ 6367844396439^4719*2000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208101589 2000000000 6367844396439 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5492785387/10000000000 : ℝ)^5743 ≤ (48231292443611/100000000000000 : ℝ)^4719 := by
    have hnat : (5492785387 : ℕ)^5743*100000000000000^4719 ≤ 48231292443611^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492785387 10000000000 48231292443611 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613250021/5000000000 : ℝ), (-208101589/2000000000 : ℝ), (5492785387/10000000000 : ℝ)] ![(45400863143361/100000000000000 : ℝ), (6367844396439/100000000000000 : ℝ), (48231292443611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613250021/5000000000 : ℝ)|^5743 ≤ (45400863143361/100000000000000 : ℝ)^4719
        have hw : |(2613250021/5000000000 : ℝ)|=(2613250021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-208101589/2000000000 : ℝ)|^5743 ≤ (6367844396439/100000000000000 : ℝ)^4719
        have hw : |(-208101589/2000000000 : ℝ)|=(208101589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5492785387/10000000000 : ℝ)|^5743 ≤ (48231292443611/100000000000000 : ℝ)^4719
        have hw : |(5492785387/10000000000 : ℝ)|=(5492785387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s3_6 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226500039/10000000000 : ℝ)*x 0 + (686598173/1250000000 : ℝ)*x 1 + (-1040507953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226500039/10000000000 : ℝ)^5743 ≤ (22700431555823/50000000000000 : ℝ)^4719 := by
    have hnat : (5226500039 : ℕ)^5743*50000000000000^4719 ≤ 22700431555823^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226500039 10000000000 22700431555823 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686598173/1250000000 : ℝ)^5743 ≤ (48231292411553/100000000000000 : ℝ)^4719 := by
    have hnat : (686598173 : ℕ)^5743*100000000000000^4719 ≤ 48231292411553^4719*1250000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686598173 1250000000 48231292411553 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040507953/10000000000 : ℝ)^5743 ≤ (3183922228011/50000000000000 : ℝ)^4719 := by
    have hnat : (1040507953 : ℕ)^5743*50000000000000^4719 ≤ 3183922228011^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040507953 10000000000 3183922228011 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226500039/10000000000 : ℝ), (686598173/1250000000 : ℝ), (-1040507953/10000000000 : ℝ)] ![(22700431555823/50000000000000 : ℝ), (48231292411553/100000000000000 : ℝ), (3183922228011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226500039/10000000000 : ℝ)|^5743 ≤ (22700431555823/50000000000000 : ℝ)^4719
        have hw : |(5226500039/10000000000 : ℝ)|=(5226500039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(686598173/1250000000 : ℝ)|^5743 ≤ (48231292411553/100000000000000 : ℝ)^4719
        have hw : |(686598173/1250000000 : ℝ)|=(686598173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1040507953/10000000000 : ℝ)|^5743 ≤ (3183922228011/50000000000000 : ℝ)^4719
        have hw : |(-1040507953/10000000000 : ℝ)|=(1040507953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s3_7 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4026220237/10000000000 : ℝ)*x 0 + (943552773/2000000000 : ℝ)*x 1 + (424558577/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4026220237/10000000000 : ℝ)^5743 ≤ (16524648143053/50000000000000 : ℝ)^4719 := by
    have hnat : (4026220237 : ℕ)^5743*50000000000000^4719 ≤ 16524648143053^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026220237 10000000000 16524648143053 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (943552773/2000000000 : ℝ)^5743 ≤ (5010124962399/12500000000000 : ℝ)^4719 := by
    have hnat : (943552773 : ℕ)^5743*12500000000000^4719 ≤ 5010124962399^4719*2000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943552773 2000000000 5010124962399 12500000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424558577/1250000000 : ℝ)^5743 ≤ (26869703999739/100000000000000 : ℝ)^4719 := by
    have hnat : (424558577 : ℕ)^5743*100000000000000^4719 ≤ 26869703999739^4719*1250000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424558577 1250000000 26869703999739 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4026220237/10000000000 : ℝ), (943552773/2000000000 : ℝ), (424558577/1250000000 : ℝ)] ![(16524648143053/50000000000000 : ℝ), (5010124962399/12500000000000 : ℝ), (26869703999739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4026220237/10000000000 : ℝ)|^5743 ≤ (16524648143053/50000000000000 : ℝ)^4719
        have hw : |(4026220237/10000000000 : ℝ)|=(4026220237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(943552773/2000000000 : ℝ)|^5743 ≤ (5010124962399/12500000000000 : ℝ)^4719
        have hw : |(943552773/2000000000 : ℝ)|=(943552773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424558577/1250000000 : ℝ)|^5743 ≤ (26869703999739/100000000000000 : ℝ)^4719
        have hw : |(424558577/1250000000 : ℝ)|=(424558577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1748_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (106469283/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9013/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4507/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9007/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (563/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9013/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (563/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9013/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (563/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9013/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (563/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9013/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (563/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9013/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (563/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9013/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9013/100000 : ℝ) ^ (5727/1024 : ℝ) ≤ (71415286714767/50000000000000000000 : ℝ) := by
    have hpowers : (9013/100000 : ℝ)^5727 ≤ (71415286714767/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9013 : ℕ)^5727*50000000000000000000^1024 ≤ 71415286714767^1024*100000^5727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9013 100000 71415286714767 50000000000000000000 5727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9013/100000 : ℝ)) (X := (71415286714767/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (563/3125 : ℝ) ^ (5727/1024 : ℝ) ≤ (3435863686184523/50000000000000000000 : ℝ) := by
    have hpowers : (563/3125 : ℝ)^5727 ≤ (3435863686184523/50000000000000000000 : ℝ)^1024 := by
      have hnat : (563 : ℕ)^5727*50000000000000000000^1024 ≤ 3435863686184523^1024*3125^5727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 3125 3435863686184523 50000000000000000000 5727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/3125 : ℝ)) (X := (3435863686184523/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000071415286714767/25000000000000000000 : ℝ) ≤ (5000002553838583/5000000000000000 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (25000071415286714767/25000000000000000000 : ℝ)^1024 ≤ (5000002553838583/5000000000000000 : ℝ)^5727 := by
      have hnat : (25000071415286714767 : ℕ)^1024*5000000000000000^5727 ≤ 5000002553838583^5727*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000071415286714767 25000000000000000000 5000002553838583 5000000000000000 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000002553838583/5000000000000000 : ℝ)) (X := (25000071415286714767/25000000000000000000 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5000350727897289929/5000000000000000000 : ℝ) ≤ (2500031354550661/2500000000000000 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (5000350727897289929/5000000000000000000 : ℝ)^1024 ≤ (2500031354550661/2500000000000000 : ℝ)^5727 := by
      have hnat : (5000350727897289929 : ℕ)^1024*2500000000000000^5727 ≤ 2500031354550661^5727*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000350727897289929 5000000000000000000 2500031354550661 2500000000000000 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500031354550661/2500000000000000 : ℝ)) (X := (5000350727897289929/5000000000000000000 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25003435863686184523/25000000000000000000 : ℝ) ≤ (5000122864364061/5000000000000000 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (25003435863686184523/25000000000000000000 : ℝ)^1024 ≤ (5000122864364061/5000000000000000 : ℝ)^5727 := by
      have hnat : (25003435863686184523 : ℕ)^1024*5000000000000000^5727 ≤ 5000122864364061^5727*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003435863686184523 25000000000000000000 5000122864364061 5000000000000000 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000122864364061/5000000000000000 : ℝ)) (X := (25003435863686184523/25000000000000000000 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(71415286714767/50000000000000000000 : ℝ) ≤ ((9002787726688525907/9003000000000000000 : ℝ)+2*(60155262739/450150000000000 : ℝ)*(9013/100000 : ℝ))^(5727/1024 : ℝ) := by
    rw [show (9002787726688525907/9003000000000000000 : ℝ)+2*(60155262739/450150000000000 : ℝ)*(9013/100000 : ℝ)=(5000002553838583/5000000000000000 : ℝ) by norm_num, show 1+2*(71415286714767/50000000000000000000 : ℝ)=(25000071415286714767/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3435863686184523/50000000000000000000 : ℝ)+(71415286714767/50000000000000000000 : ℝ) ≤ ((9002787726688525907/9003000000000000000 : ℝ)+(60155262739/450150000000000 : ℝ)*((563/3125 : ℝ)+(9013/100000 : ℝ)))^(5727/1024 : ℝ) := by
    rw [show (9002787726688525907/9003000000000000000 : ℝ)+(60155262739/450150000000000 : ℝ)*((563/3125 : ℝ)+(9013/100000 : ℝ))=(2500031354550661/2500000000000000 : ℝ) by norm_num, show 1+(3435863686184523/50000000000000000000 : ℝ)+(71415286714767/50000000000000000000 : ℝ)=(5000350727897289929/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3435863686184523/50000000000000000000 : ℝ) ≤ ((9002787726688525907/9003000000000000000 : ℝ)+2*(60155262739/450150000000000 : ℝ)*(563/3125 : ℝ))^(5727/1024 : ℝ) := by
    rw [show (9002787726688525907/9003000000000000000 : ℝ)+2*(60155262739/450150000000000 : ℝ)*(563/3125 : ℝ)=(5000122864364061/5000000000000000 : ℝ) by norm_num, show 1+2*(3435863686184523/50000000000000000000 : ℝ)=(25003435863686184523/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9002787726688525907/9003000000000000000 : ℝ)*(X 1 0+X 2 0)+(60155262739/450150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (9013/100000 : ℝ)) (hi := (563/3125 : ℝ)) (c := (9002787726688525907/9003000000000000000 : ℝ)) (alpha := (60155262739/450150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9002787726688525907/9003000000000000000 : ℝ)*(X 0 1+X 2 1)+(60155262739/450150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (9013/100000 : ℝ)) (hi := (563/3125 : ℝ)) (c := (9002787726688525907/9003000000000000000 : ℝ)) (alpha := (60155262739/450150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9002787726688525907/9003000000000000000 : ℝ)*(X 0 2+X 1 2)+(60155262739/450150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (9013/100000 : ℝ)) (hi := (563/3125 : ℝ)) (c := (9002787726688525907/9003000000000000000 : ℝ)) (alpha := (60155262739/450150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-154175171/1250000000 : ℝ)*X 0 0+(5499724001/10000000000 : ℝ)*X 0 1+(101610623/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5337682617/10000000000 : ℝ)*X 1 0+(-1452761473/10000000000 : ℝ)*X 1 1+(635066481/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5337682407/10000000000 : ℝ)*X 2 0+(5080531971/10000000000 : ℝ)*X 2 1+(-145276159/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((402506343/1000000000 : ℝ)*X 0 0+(1686928749/5000000000 : ℝ)*X 0 1+(1184977503/2500000000 : ℝ)*X 0 2+(402506343/1000000000 : ℝ)*X 1 0+(1686928749/5000000000 : ℝ)*X 1 1+(1184977503/2500000000 : ℝ)*X 1 2+(402506343/1000000000 : ℝ)*X 2 0+(1686928749/5000000000 : ℝ)*X 2 1+(1184977503/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-246751223/2000000000 : ℝ)*X 0 0+(2543663633/5000000000 : ℝ)*X 0 1+(5492785407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2613250021/5000000000 : ℝ)*X 1 0+(-208101589/2000000000 : ℝ)*X 1 1+(5492785387/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5226500039/10000000000 : ℝ)*X 2 0+(686598173/1250000000 : ℝ)*X 2 1+(-1040507953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4026220237/10000000000 : ℝ)*X 0 0+(943552773/2000000000 : ℝ)*X 0 1+(424558577/1250000000 : ℝ)*X 0 2+(4026220237/10000000000 : ℝ)*X 1 0+(943552773/2000000000 : ℝ)*X 1 1+(424558577/1250000000 : ℝ)*X 1 2+(4026220237/10000000000 : ℝ)*X 2 0+(943552773/2000000000 : ℝ)*X 2 1+(424558577/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3781676036507552776869/300100000000000000000000000 : ℝ) := by norm_num
    linear_combination (1794329809/100000000000000 : ℝ)*(base19) + (13576469/800000000000 : ℝ)*(base23) + (337811903/100000000000000 : ℝ)*(upper3) + (1823291/100000000000000 : ℝ)*(upper4) + (264354149/100000000000000 : ℝ)*(upper5) + (311761916933823/20000000000000 : ℝ)*(major0) + (311761916933823/20000000000000 : ℝ)*(major1) + (311761916933823/20000000000000 : ℝ)*(major2) + (596388717015693/25000000000000 : ℝ)*(sp0) + (95422813218349/4000000000000 : ℝ)*(sp1) + (596392606932477/25000000000000 : ℝ)*(sp2) + (183010312243031/25000000000000 : ℝ)*(sp3) + (17256725761/100000000000000 : ℝ)*(sp4) + (1343882839/25000000000000 : ℝ)*(sp7) + (18301165612587/2500000000000 : ℝ)*(f.failure) + (1192786062394267/50000000000000 : ℝ)*(f.sum) + (9312131611717/3001000000000000000000000000 : ℝ)*base65 + (286306869250197487/60020000000000000000000000000000 : ℝ)*base67 + (197848227601777487/60020000000000000000000000000000 : ℝ)*base69 + (4540035032342513/60020000000000000000000000000000 : ℝ)*base72 + (5667991245031/3001000000000000000000000000 : ℝ)*base73 + (455700925903682513/60020000000000000000000000000000 : ℝ)*base76 + (173246965796962513/60020000000000000000000000000000 : ℝ)*base78 + (215243281080797487/60020000000000000000000000000000 : ℝ)*base79 + (984088746867/1500500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (84879/125000000000000000000 : ℝ)*base90 + (84879/125000000000000000000 : ℝ)*base92 + (84879/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (476641078968201884162058471/75025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (413512601/50000000000000 : ℝ)*(base19) + (887487209/100000000000000 : ℝ)*(base23) + (233792059/100000000000000 : ℝ)*(lower1) + (16754159/12500000000000 : ℝ)*(upper3) + (5753559/20000000000000 : ℝ)*(lower4) + (136159727/100000000000000 : ℝ)*(upper5) + (805792818777747/50000000000000 : ℝ)*(major0) + (805792818777747/50000000000000 : ℝ)*(major1) + (805792818777747/50000000000000 : ℝ)*(major2) + (321325007/100000000000000 : ℝ)*(sp2) + (1233169900385721/50000000000000 : ℝ)*(sp4) + (7707309292957/312500000000 : ℝ)*(sp5) + (1233169295979613/50000000000000 : ℝ)*(sp6) + (189207815642411/25000000000000 : ℝ)*(sp7) + (189207815642411/25000000000000 : ℝ)*(f.failure) + (1233169900385721/50000000000000 : ℝ)*(f.sum) + (50792070383473/7502500000000000000000000000 : ℝ)*base66 + (10068851373483843/150050000000000000000000000000000 : ℝ)*base67 + (100715862075183843/150050000000000000000000000000000 : ℝ)*base69 + (10333489263830316157/150050000000000000000000000000000 : ℝ)*base72 + (1748608762859/937812500000000000000000000 : ℝ)*base73 + (4638490751775883843/150050000000000000000000000000000 : ℝ)*base75 + (723527242740533843/150050000000000000000000000000000 : ℝ)*base77 + (428274315676966157/150050000000000000000000000000000 : ℝ)*base80 + (253063440123/468906250000000000000000000 : ℝ)*base82 + (8561313/1250000000000000000000 : ℝ)*base89 + (8561313/1250000000000000000000 : ℝ)*base91 + (8561313/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1748_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (106469283/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9013/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4507/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9007/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1748_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1748_box_0 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-168671969/2000000000 : ℝ)*x 0 + (2713740699/5000000000 : ℝ)*x 1 + (1356870361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168671969/2000000000 : ℝ)^5743 ≤ (4931317406657/100000000000000 : ℝ)^4719 := by
    have hnat : (168671969 : ℕ)^5743*100000000000000^4719 ≤ 4931317406657^4719*2000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168671969 2000000000 4931317406657 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713740699/5000000000 : ℝ)^5743 ≤ (47534341041447/100000000000000 : ℝ)^4719 := by
    have hnat : (2713740699 : ℕ)^5743*100000000000000^4719 ≤ 47534341041447^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713740699 5000000000 47534341041447 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356870361/2500000000 : ℝ)^5743 ≤ (2376717076587/5000000000000 : ℝ)^4719 := by
    have hnat : (1356870361 : ℕ)^5743*5000000000000^4719 ≤ 2376717076587^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356870361 2500000000 2376717076587 5000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-168671969/2000000000 : ℝ), (2713740699/5000000000 : ℝ), (1356870361/2500000000 : ℝ)] ![(4931317406657/100000000000000 : ℝ), (47534341041447/100000000000000 : ℝ), (2376717076587/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-168671969/2000000000 : ℝ)|^5743 ≤ (4931317406657/100000000000000 : ℝ)^4719
        have hw : |(-168671969/2000000000 : ℝ)|=(168671969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713740699/5000000000 : ℝ)|^5743 ≤ (47534341041447/100000000000000 : ℝ)^4719
        have hw : |(2713740699/5000000000 : ℝ)|=(2713740699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356870361/2500000000 : ℝ)|^5743 ≤ (2376717076587/5000000000000 : ℝ)^4719
        have hw : |(1356870361/2500000000 : ℝ)|=(1356870361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_1 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298649407/2500000000 : ℝ)*x 0 + (-294361253/2500000000 : ℝ)*x 1 + (5427481367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298649407/2500000000 : ℝ)^5743 ≤ (45063826311877/100000000000000 : ℝ)^4719 := by
    have hnat : (1298649407 : ℕ)^5743*100000000000000^4719 ≤ 45063826311877^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298649407 2500000000 45063826311877 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294361253/2500000000 : ℝ)^5743 ≤ (7401832960699/100000000000000 : ℝ)^4719 := by
    have hnat : (294361253 : ℕ)^5743*100000000000000^4719 ≤ 7401832960699^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294361253 2500000000 7401832960699 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427481367/10000000000 : ℝ)^5743 ≤ (5941792588879/12500000000000 : ℝ)^4719 := by
    have hnat : (5427481367 : ℕ)^5743*12500000000000^4719 ≤ 5941792588879^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427481367 10000000000 5941792588879 12500000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298649407/2500000000 : ℝ), (-294361253/2500000000 : ℝ), (5427481367/10000000000 : ℝ)] ![(45063826311877/100000000000000 : ℝ), (7401832960699/100000000000000 : ℝ), (5941792588879/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298649407/2500000000 : ℝ)|^5743 ≤ (45063826311877/100000000000000 : ℝ)^4719
        have hw : |(1298649407/2500000000 : ℝ)|=(1298649407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-294361253/2500000000 : ℝ)|^5743 ≤ (7401832960699/100000000000000 : ℝ)^4719
        have hw : |(-294361253/2500000000 : ℝ)|=(294361253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427481367/10000000000 : ℝ)|^5743 ≤ (5941792588879/12500000000000 : ℝ)^4719
        have hw : |(5427481367/10000000000 : ℝ)|=(5427481367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_2 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038919507/2000000000 : ℝ)*x 0 + (5427481453/10000000000 : ℝ)*x 1 + (-588722511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038919507/2000000000 : ℝ)^5743 ≤ (2253191266501/5000000000000 : ℝ)^4719 := by
    have hnat : (1038919507 : ℕ)^5743*5000000000000^4719 ≤ 2253191266501^4719*2000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038919507 2000000000 2253191266501 5000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427481453/10000000000 : ℝ)^5743 ≤ (47534341627667/100000000000000 : ℝ)^4719 := by
    have hnat : (5427481453 : ℕ)^5743*100000000000000^4719 ≤ 47534341627667^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427481453 10000000000 47534341627667 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (588722511/5000000000 : ℝ)^5743 ≤ (1850458259301/25000000000000 : ℝ)^4719 := by
    have hnat : (588722511 : ℕ)^5743*25000000000000^4719 ≤ 1850458259301^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588722511 5000000000 1850458259301 25000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038919507/2000000000 : ℝ), (5427481453/10000000000 : ℝ), (-588722511/5000000000 : ℝ)] ![(2253191266501/5000000000000 : ℝ), (47534341627667/100000000000000 : ℝ), (1850458259301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038919507/2000000000 : ℝ)|^5743 ≤ (2253191266501/5000000000000 : ℝ)^4719
        have hw : |(1038919507/2000000000 : ℝ)|=(1038919507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427481453/10000000000 : ℝ)|^5743 ≤ (47534341627667/100000000000000 : ℝ)^4719
        have hw : |(5427481453/10000000000 : ℝ)|=(5427481453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-588722511/5000000000 : ℝ)|^5743 ≤ (1850458259301/25000000000000 : ℝ)^4719
        have hw : |(-588722511/5000000000 : ℝ)|=(588722511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_3 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4551784083/10000000000 : ℝ)*x 0 + (3801099753/10000000000 : ℝ)*x 1 + (1900549881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4551784083/10000000000 : ℝ)^5743 ≤ (9592874132263/25000000000000 : ℝ)^4719 := by
    have hnat : (4551784083 : ℕ)^5743*25000000000000^4719 ≤ 9592874132263^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551784083 10000000000 9592874132263 25000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3801099753/10000000000 : ℝ)^5743 ≤ (1925890730209/6250000000000 : ℝ)^4719 := by
    have hnat : (3801099753 : ℕ)^5743*6250000000000^4719 ≤ 1925890730209^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3801099753 10000000000 1925890730209 6250000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1900549881/5000000000 : ℝ)^5743 ≤ (6162850354427/20000000000000 : ℝ)^4719 := by
    have hnat : (1900549881 : ℕ)^5743*20000000000000^4719 ≤ 6162850354427^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900549881 5000000000 6162850354427 20000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4551784083/10000000000 : ℝ), (3801099753/10000000000 : ℝ), (1900549881/5000000000 : ℝ)] ![(9592874132263/25000000000000 : ℝ), (1925890730209/6250000000000 : ℝ), (6162850354427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4551784083/10000000000 : ℝ)|^5743 ≤ (9592874132263/25000000000000 : ℝ)^4719
        have hw : |(4551784083/10000000000 : ℝ)|=(4551784083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3801099753/10000000000 : ℝ)|^5743 ≤ (1925890730209/6250000000000 : ℝ)^4719
        have hw : |(3801099753/10000000000 : ℝ)|=(3801099753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1900549881/5000000000 : ℝ)|^5743 ≤ (6162850354427/20000000000000 : ℝ)^4719
        have hw : |(1900549881/5000000000 : ℝ)|=(1900549881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_4 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1663327553/10000000000 : ℝ)*x 0 + (5128301737/10000000000 : ℝ)*x 1 + (1282075373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1663327553/10000000000 : ℝ)^5743 ≤ (704390961337/6250000000000 : ℝ)^4719 := by
    have hnat : (1663327553 : ℕ)^5743*6250000000000^4719 ≤ 704390961337^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663327553 10000000000 704390961337 6250000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128301737/10000000000 : ℝ)^5743 ≤ (4436487358777/10000000000000 : ℝ)^4719 := by
    have hnat : (5128301737 : ℕ)^5743*10000000000000^4719 ≤ 4436487358777^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128301737 10000000000 4436487358777 10000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1282075373/2500000000 : ℝ)^5743 ≤ (44364871008359/100000000000000 : ℝ)^4719 := by
    have hnat : (1282075373 : ℕ)^5743*100000000000000^4719 ≤ 44364871008359^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282075373 2500000000 44364871008359 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1663327553/10000000000 : ℝ), (5128301737/10000000000 : ℝ), (1282075373/2500000000 : ℝ)] ![(704390961337/6250000000000 : ℝ), (4436487358777/10000000000000 : ℝ), (44364871008359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1663327553/10000000000 : ℝ)|^5743 ≤ (704390961337/6250000000000 : ℝ)^4719
        have hw : |(-1663327553/10000000000 : ℝ)|=(1663327553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128301737/10000000000 : ℝ)|^5743 ≤ (4436487358777/10000000000000 : ℝ)^4719
        have hw : |(5128301737/10000000000 : ℝ)|=(5128301737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1282075373/2500000000 : ℝ)|^5743 ≤ (44364871008359/100000000000000 : ℝ)^4719
        have hw : |(1282075373/2500000000 : ℝ)|=(1282075373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_5 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395043763/10000000000 : ℝ)*x 0 + (-656169709/5000000000 : ℝ)*x 1 + (320518853/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395043763/10000000000 : ℝ)^5743 ≤ (47188827550897/100000000000000 : ℝ)^4719 := by
    have hnat : (5395043763 : ℕ)^5743*100000000000000^4719 ≤ 47188827550897^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395043763 10000000000 47188827550897 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656169709/5000000000 : ℝ)^5743 ≤ (844629978769/10000000000000 : ℝ)^4719 := by
    have hnat : (656169709 : ℕ)^5743*10000000000000^4719 ≤ 844629978769^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656169709 5000000000 844629978769 10000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320518853/625000000 : ℝ)^5743 ≤ (44364872650759/100000000000000 : ℝ)^4719 := by
    have hnat : (320518853 : ℕ)^5743*100000000000000^4719 ≤ 44364872650759^4719*625000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320518853 625000000 44364872650759 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395043763/10000000000 : ℝ), (-656169709/5000000000 : ℝ), (320518853/625000000 : ℝ)] ![(47188827550897/100000000000000 : ℝ), (844629978769/10000000000000 : ℝ), (44364872650759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395043763/10000000000 : ℝ)|^5743 ≤ (47188827550897/100000000000000 : ℝ)^4719
        have hw : |(5395043763/10000000000 : ℝ)|=(5395043763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-656169709/5000000000 : ℝ)|^5743 ≤ (844629978769/10000000000000 : ℝ)^4719
        have hw : |(-656169709/5000000000 : ℝ)|=(656169709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(320518853/625000000 : ℝ)|^5743 ≤ (44364872650759/100000000000000 : ℝ)^4719
        have hw : |(320518853/625000000 : ℝ)|=(320518853/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_6 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348760967/2500000000 : ℝ)*x 0 + (5128301503/10000000000 : ℝ)*x 1 + (-1312339469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348760967/2500000000 : ℝ)^5743 ≤ (4718882866859/10000000000000 : ℝ)^4719 := by
    have hnat : (1348760967 : ℕ)^5743*10000000000000^4719 ≤ 4718882866859^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348760967 2500000000 4718882866859 10000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128301503/10000000000 : ℝ)^5743 ≤ (44364871124169/100000000000000 : ℝ)^4719 := by
    have hnat : (5128301503 : ℕ)^5743*100000000000000^4719 ≤ 44364871124169^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128301503 10000000000 44364871124169 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1312339469/10000000000 : ℝ)^5743 ≤ (2111575046789/25000000000000 : ℝ)^4719 := by
    have hnat : (1312339469 : ℕ)^5743*25000000000000^4719 ≤ 2111575046789^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312339469 10000000000 2111575046789 25000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348760967/2500000000 : ℝ), (5128301503/10000000000 : ℝ), (-1312339469/10000000000 : ℝ)] ![(4718882866859/10000000000000 : ℝ), (44364871124169/100000000000000 : ℝ), (2111575046789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348760967/2500000000 : ℝ)|^5743 ≤ (4718882866859/10000000000000 : ℝ)^4719
        have hw : |(1348760967/2500000000 : ℝ)|=(1348760967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128301503/10000000000 : ℝ)|^5743 ≤ (44364871124169/100000000000000 : ℝ)^4719
        have hw : |(5128301503/10000000000 : ℝ)|=(5128301503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1312339469/10000000000 : ℝ)|^5743 ≤ (2111575046789/25000000000000 : ℝ)^4719
        have hw : |(-1312339469/10000000000 : ℝ)|=(1312339469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_7 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (173103453/500000000 : ℝ)*x 0 + (2171912661/5000000000 : ℝ)*x 1 + (2171912581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173103453/500000000 : ℝ)^5743 ≤ (27502604575333/100000000000000 : ℝ)^4719 := by
    have hnat : (173103453 : ℕ)^5743*100000000000000^4719 ≤ 27502604575333^4719*500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173103453 500000000 27502604575333 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2171912661/5000000000 : ℝ)^5743 ≤ (362486985187/1000000000000 : ℝ)^4719 := by
    have hnat : (2171912661 : ℕ)^5743*1000000000000^4719 ≤ 362486985187^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171912661 5000000000 362486985187 1000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2171912581/5000000000 : ℝ)^5743 ≤ (36248696893791/100000000000000 : ℝ)^4719 := by
    have hnat : (2171912581 : ℕ)^5743*100000000000000^4719 ≤ 36248696893791^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171912581 5000000000 36248696893791 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173103453/500000000 : ℝ), (2171912661/5000000000 : ℝ), (2171912581/5000000000 : ℝ)] ![(27502604575333/100000000000000 : ℝ), (362486985187/1000000000000 : ℝ), (36248696893791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173103453/500000000 : ℝ)|^5743 ≤ (27502604575333/100000000000000 : ℝ)^4719
        have hw : |(173103453/500000000 : ℝ)|=(173103453/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2171912661/5000000000 : ℝ)|^5743 ≤ (362486985187/1000000000000 : ℝ)^4719
        have hw : |(2171912661/5000000000 : ℝ)|=(2171912661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2171912581/5000000000 : ℝ)|^5743 ≤ (36248696893791/100000000000000 : ℝ)^4719
        have hw : |(2171912581/5000000000 : ℝ)|=(2171912581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_8 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1485063269/10000000000 : ℝ)*x 0 + (196028407/400000000 : ℝ)*x 1 + (5490016563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1485063269/10000000000 : ℝ)^5743 ≤ (4908939201629/50000000000000 : ℝ)^4719 := by
    have hnat : (1485063269 : ℕ)^5743*50000000000000^4719 ≤ 4908939201629^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1485063269 10000000000 4908939201629 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196028407/400000000 : ℝ)^5743 ≤ (10495103960293/25000000000000 : ℝ)^4719 := by
    have hnat : (196028407 : ℕ)^5743*25000000000000^4719 ≤ 10495103960293^4719*400000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196028407 400000000 10495103960293 25000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490016563/10000000000 : ℝ)^5743 ≤ (12050426432931/25000000000000 : ℝ)^4719 := by
    have hnat : (5490016563 : ℕ)^5743*25000000000000^4719 ≤ 12050426432931^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490016563 10000000000 12050426432931 25000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1485063269/10000000000 : ℝ), (196028407/400000000 : ℝ), (5490016563/10000000000 : ℝ)] ![(4908939201629/50000000000000 : ℝ), (10495103960293/25000000000000 : ℝ), (12050426432931/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1485063269/10000000000 : ℝ)|^5743 ≤ (4908939201629/50000000000000 : ℝ)^4719
        have hw : |(-1485063269/10000000000 : ℝ)|=(1485063269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(196028407/400000000 : ℝ)|^5743 ≤ (10495103960293/25000000000000 : ℝ)^4719
        have hw : |(196028407/400000000 : ℝ)|=(196028407/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490016563/10000000000 : ℝ)|^5743 ≤ (12050426432931/25000000000000 : ℝ)^4719
        have hw : |(5490016563/10000000000 : ℝ)|=(5490016563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_9 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (644095391/1250000000 : ℝ)*x 0 + (-1147808967/10000000000 : ℝ)*x 1 + (5490018997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (644095391/1250000000 : ℝ)^5743 ≤ (2788908834381/6250000000000 : ℝ)^4719 := by
    have hnat : (644095391 : ℕ)^5743*6250000000000^4719 ≤ 2788908834381^4719*1250000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644095391 1250000000 2788908834381 6250000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1147808967/10000000000 : ℝ)^5743 ≤ (448482931091/6250000000000 : ℝ)^4719 := by
    have hnat : (1147808967 : ℕ)^5743*6250000000000^4719 ≤ 448482931091^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147808967 10000000000 448482931091 6250000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490018997/10000000000 : ℝ)^5743 ≤ (48201731739199/100000000000000 : ℝ)^4719 := by
    have hnat : (5490018997 : ℕ)^5743*100000000000000^4719 ≤ 48201731739199^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490018997 10000000000 48201731739199 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(644095391/1250000000 : ℝ), (-1147808967/10000000000 : ℝ), (5490018997/10000000000 : ℝ)] ![(2788908834381/6250000000000 : ℝ), (448482931091/6250000000000 : ℝ), (48201731739199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(644095391/1250000000 : ℝ)|^5743 ≤ (2788908834381/6250000000000 : ℝ)^4719
        have hw : |(644095391/1250000000 : ℝ)|=(644095391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1147808967/10000000000 : ℝ)|^5743 ≤ (448482931091/6250000000000 : ℝ)^4719
        have hw : |(-1147808967/10000000000 : ℝ)|=(1147808967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490018997/10000000000 : ℝ)|^5743 ≤ (48201731739199/100000000000000 : ℝ)^4719
        have hw : |(5490018997/10000000000 : ℝ)|=(5490018997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_10 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103055279/200000000 : ℝ)*x 0 + (1372504607/2500000000 : ℝ)*x 1 + (-286952157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103055279/200000000 : ℝ)^5743 ≤ (22311275006613/50000000000000 : ℝ)^4719 := by
    have hnat : (103055279 : ℕ)^5743*50000000000000^4719 ≤ 22311275006613^4719*200000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103055279 200000000 22311275006613 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372504607/2500000000 : ℝ)^5743 ≤ (48201725659391/100000000000000 : ℝ)^4719 := by
    have hnat : (1372504607 : ℕ)^5743*100000000000000^4719 ≤ 48201725659391^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372504607 2500000000 48201725659391 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (286952157/2500000000 : ℝ)^5743 ≤ (7175724318257/100000000000000 : ℝ)^4719 := by
    have hnat : (286952157 : ℕ)^5743*100000000000000^4719 ≤ 7175724318257^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286952157 2500000000 7175724318257 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103055279/200000000 : ℝ), (1372504607/2500000000 : ℝ), (-286952157/2500000000 : ℝ)] ![(22311275006613/50000000000000 : ℝ), (48201725659391/100000000000000 : ℝ), (7175724318257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103055279/200000000 : ℝ)|^5743 ≤ (22311275006613/50000000000000 : ℝ)^4719
        have hw : |(103055279/200000000 : ℝ)|=(103055279/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372504607/2500000000 : ℝ)|^5743 ≤ (48201725659391/100000000000000 : ℝ)^4719
        have hw : |(1372504607/2500000000 : ℝ)|=(1372504607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-286952157/2500000000 : ℝ)|^5743 ≤ (7175724318257/100000000000000 : ℝ)^4719
        have hw : |(-286952157/2500000000 : ℝ)|=(286952157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_11 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4768957729/10000000000 : ℝ)*x 0 + (3687231901/10000000000 : ℝ)*x 1 + (3687231439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4768957729/10000000000 : ℝ)^5743 ≤ (40610929894959/100000000000000 : ℝ)^4719 := by
    have hnat : (4768957729 : ℕ)^5743*100000000000000^4719 ≤ 40610929894959^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4768957729 10000000000 40610929894959 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3687231901/10000000000 : ℝ)^5743 ≤ (29694537307619/100000000000000 : ℝ)^4719 := by
    have hnat : (3687231901 : ℕ)^5743*100000000000000^4719 ≤ 29694537307619^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3687231901 10000000000 29694537307619 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3687231439/10000000000 : ℝ)^5743 ≤ (14847266389807/50000000000000 : ℝ)^4719 := by
    have hnat : (3687231439 : ℕ)^5743*50000000000000^4719 ≤ 14847266389807^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3687231439 10000000000 14847266389807 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4768957729/10000000000 : ℝ), (3687231901/10000000000 : ℝ), (3687231439/10000000000 : ℝ)] ![(40610929894959/100000000000000 : ℝ), (29694537307619/100000000000000 : ℝ), (14847266389807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4768957729/10000000000 : ℝ)|^5743 ≤ (40610929894959/100000000000000 : ℝ)^4719
        have hw : |(4768957729/10000000000 : ℝ)|=(4768957729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3687231901/10000000000 : ℝ)|^5743 ≤ (29694537307619/100000000000000 : ℝ)^4719
        have hw : |(3687231901/10000000000 : ℝ)|=(3687231901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3687231439/10000000000 : ℝ)|^5743 ≤ (14847266389807/50000000000000 : ℝ)^4719
        have hw : |(3687231439/10000000000 : ℝ)|=(3687231439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_12 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-504015941/5000000000 : ℝ)*x 0 + (5641594381/10000000000 : ℝ)*x 1 + (2549048057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (504015941/5000000000 : ℝ)^5743 ≤ (1225358131237/20000000000000 : ℝ)^4719 := by
    have hnat : (504015941 : ℕ)^5743*20000000000000^4719 ≤ 1225358131237^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504015941 5000000000 1225358131237 20000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5641594381/10000000000 : ℝ)^5743 ≤ (24913071661203/50000000000000 : ℝ)^4719 := by
    have hnat : (5641594381 : ℕ)^5743*50000000000000^4719 ≤ 24913071661203^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5641594381 10000000000 24913071661203 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2549048057/5000000000 : ℝ)^5743 ≤ (11011766499883/25000000000000 : ℝ)^4719 := by
    have hnat : (2549048057 : ℕ)^5743*25000000000000^4719 ≤ 11011766499883^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2549048057 5000000000 11011766499883 25000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-504015941/5000000000 : ℝ), (5641594381/10000000000 : ℝ), (2549048057/5000000000 : ℝ)] ![(1225358131237/20000000000000 : ℝ), (24913071661203/50000000000000 : ℝ), (11011766499883/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-504015941/5000000000 : ℝ)|^5743 ≤ (1225358131237/20000000000000 : ℝ)^4719
        have hw : |(-504015941/5000000000 : ℝ)|=(504015941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5641594381/10000000000 : ℝ)|^5743 ≤ (24913071661203/50000000000000 : ℝ)^4719
        have hw : |(5641594381/10000000000 : ℝ)|=(5641594381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2549048057/5000000000 : ℝ)|^5743 ≤ (11011766499883/25000000000000 : ℝ)^4719
        have hw : |(2549048057/5000000000 : ℝ)|=(2549048057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_13 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5415352849/10000000000 : ℝ)*x 0 + (-265057459/2000000000 : ℝ)*x 1 + (5098097057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415352849/10000000000 : ℝ)^5743 ≤ (9481019940469/20000000000000 : ℝ)^4719 := by
    have hnat : (5415352849 : ℕ)^5743*20000000000000^4719 ≤ 9481019940469^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415352849 10000000000 9481019940469 20000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265057459/2000000000 : ℝ)^5743 ≤ (8547824362647/100000000000000 : ℝ)^4719 := by
    have hnat : (265057459 : ℕ)^5743*100000000000000^4719 ≤ 8547824362647^4719*2000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265057459 2000000000 8547824362647 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5098097057/10000000000 : ℝ)^5743 ≤ (8809415182983/20000000000000 : ℝ)^4719 := by
    have hnat : (5098097057 : ℕ)^5743*20000000000000^4719 ≤ 8809415182983^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098097057 10000000000 8809415182983 20000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415352849/10000000000 : ℝ), (-265057459/2000000000 : ℝ), (5098097057/10000000000 : ℝ)] ![(9481019940469/20000000000000 : ℝ), (8547824362647/100000000000000 : ℝ), (8809415182983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415352849/10000000000 : ℝ)|^5743 ≤ (9481019940469/20000000000000 : ℝ)^4719
        have hw : |(5415352849/10000000000 : ℝ)|=(5415352849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265057459/2000000000 : ℝ)|^5743 ≤ (8547824362647/100000000000000 : ℝ)^4719
        have hw : |(-265057459/2000000000 : ℝ)|=(265057459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5098097057/10000000000 : ℝ)|^5743 ≤ (8809415182983/20000000000000 : ℝ)^4719
        have hw : |(5098097057/10000000000 : ℝ)|=(5098097057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_14 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5415352957/10000000000 : ℝ)*x 0 + (203923867/400000000 : ℝ)*x 1 + (-1325287661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415352957/10000000000 : ℝ)^5743 ≤ (47405100852909/100000000000000 : ℝ)^4719 := by
    have hnat : (5415352957 : ℕ)^5743*100000000000000^4719 ≤ 47405100852909^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415352957 10000000000 47405100852909 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203923867/400000000 : ℝ)^5743 ≤ (44047071898291/100000000000000 : ℝ)^4719 := by
    have hnat : (203923867 : ℕ)^5743*100000000000000^4719 ≤ 44047071898291^4719*400000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203923867 400000000 44047071898291 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1325287661/10000000000 : ℝ)^5743 ≤ (4273913617757/50000000000000 : ℝ)^4719 := by
    have hnat : (1325287661 : ℕ)^5743*50000000000000^4719 ≤ 4273913617757^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325287661 10000000000 4273913617757 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415352957/10000000000 : ℝ), (203923867/400000000 : ℝ), (-1325287661/10000000000 : ℝ)] ![(47405100852909/100000000000000 : ℝ), (44047071898291/100000000000000 : ℝ), (4273913617757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415352957/10000000000 : ℝ)|^5743 ≤ (47405100852909/100000000000000 : ℝ)^4719
        have hw : |(5415352957/10000000000 : ℝ)|=(5415352957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(203923867/400000000 : ℝ)|^5743 ≤ (44047071898291/100000000000000 : ℝ)^4719
        have hw : |(203923867/400000000 : ℝ)|=(203923867/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1325287661/10000000000 : ℝ)|^5743 ≤ (4273913617757/50000000000000 : ℝ)^4719
        have hw : |(-1325287661/10000000000 : ℝ)|=(1325287661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_box_15 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (836710543/2500000000 : ℝ)*x 0 + (4398398013/10000000000 : ℝ)*x 1 + (4398395809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836710543/2500000000 : ℝ)^5743 ≤ (13196337049993/50000000000000 : ℝ)^4719 := by
    have hnat : (836710543 : ℕ)^5743*50000000000000^4719 ≤ 13196337049993^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836710543 2500000000 13196337049993 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4398398013/10000000000 : ℝ)^5743 ≤ (36803674162359/100000000000000 : ℝ)^4719 := by
    have hnat : (4398398013 : ℕ)^5743*100000000000000^4719 ≤ 36803674162359^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4398398013 10000000000 36803674162359 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4398395809/10000000000 : ℝ)^5743 ≤ (9200912929631/25000000000000 : ℝ)^4719 := by
    have hnat : (4398395809 : ℕ)^5743*25000000000000^4719 ≤ 9200912929631^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4398395809 10000000000 9200912929631 25000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836710543/2500000000 : ℝ), (4398398013/10000000000 : ℝ), (4398395809/10000000000 : ℝ)] ![(13196337049993/50000000000000 : ℝ), (36803674162359/100000000000000 : ℝ), (9200912929631/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836710543/2500000000 : ℝ)|^5743 ≤ (13196337049993/50000000000000 : ℝ)^4719
        have hw : |(836710543/2500000000 : ℝ)|=(836710543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4398398013/10000000000 : ℝ)|^5743 ≤ (36803674162359/100000000000000 : ℝ)^4719
        have hw : |(4398398013/10000000000 : ℝ)|=(4398398013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4398395809/10000000000 : ℝ)|^5743 ≤ (9200912929631/25000000000000 : ℝ)^4719
        have hw : |(4398395809/10000000000 : ℝ)|=(4398395809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1748_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (106469283/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4507/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(551/800 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58013/100000 : ℝ) ∧ (81449/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (46431/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9007/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4507/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9007/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4507/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9007/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4507/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9007/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4507/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9007/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4507/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9007/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4507/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4507/50000 : ℝ) ^ (5727/1024 : ℝ) ≤ (142919225664321/100000000000000000000 : ℝ) := by
    have hpowers : (4507/50000 : ℝ)^5727 ≤ (142919225664321/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4507 : ℕ)^5727*100000000000000000000^1024 ≤ 142919225664321^1024*50000^5727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4507 50000 142919225664321 100000000000000000000 5727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4507/50000 : ℝ)) (X := (142919225664321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9007/50000 : ℝ) ^ (5727/1024 : ℝ) ≤ (1716865507106363/25000000000000000000 : ℝ) := by
    have hpowers : (9007/50000 : ℝ)^5727 ≤ (1716865507106363/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9007 : ℕ)^5727*25000000000000000000^1024 ≤ 1716865507106363^1024*50000^5727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9007 50000 1716865507106363 25000000000000000000 5727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9007/50000 : ℝ)) (X := (1716865507106363/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000142919225664321/50000000000000000000 : ℝ) ≤ (10000005110847401/10000000000000000 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (50000142919225664321/50000000000000000000 : ℝ)^1024 ≤ (10000005110847401/10000000000000000 : ℝ)^5727 := by
      have hnat : (50000142919225664321 : ℕ)^1024*10000000000000000^5727 ≤ 10000005110847401^5727*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000142919225664321 50000000000000000000 10000005110847401 10000000000000000 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000005110847401/10000000000000000 : ℝ)) (X := (50000142919225664321/50000000000000000000 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100007010381254089773/100000000000000000000 : ℝ) ≤ (1250015667940849/1250000000000000 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (100007010381254089773/100000000000000000000 : ℝ)^1024 ≤ (1250015667940849/1250000000000000 : ℝ)^5727 := by
      have hnat : (100007010381254089773 : ℕ)^1024*1250000000000000^5727 ≤ 1250015667940849^5727*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100007010381254089773 100000000000000000000 1250015667940849 1250000000000000 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250015667940849/1250000000000000 : ℝ)) (X := (100007010381254089773/100000000000000000000 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12501716865507106363/12500000000000000000 : ℝ) ≤ (10000245576206183/10000000000000000 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (12501716865507106363/12500000000000000000 : ℝ)^1024 ≤ (10000245576206183/10000000000000000 : ℝ)^5727 := by
      have hnat : (12501716865507106363 : ℕ)^1024*10000000000000000^5727 ≤ 10000245576206183^5727*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501716865507106363 12500000000000000000 10000245576206183 10000000000000000 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000245576206183/10000000000000000 : ℝ)) (X := (12501716865507106363/12500000000000000000 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(142919225664321/100000000000000000000 : ℝ) ≤ ((2499941067857848557/2500000000000000000 : ℝ)+2*(13359186599/100000000000000 : ℝ)*(4507/50000 : ℝ))^(5727/1024 : ℝ) := by
    rw [show (2499941067857848557/2500000000000000000 : ℝ)+2*(13359186599/100000000000000 : ℝ)*(4507/50000 : ℝ)=(10000005110847401/10000000000000000 : ℝ) by norm_num, show 1+2*(142919225664321/100000000000000000000 : ℝ)=(50000142919225664321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1716865507106363/25000000000000000000 : ℝ)+(142919225664321/100000000000000000000 : ℝ) ≤ ((2499941067857848557/2500000000000000000 : ℝ)+(13359186599/100000000000000 : ℝ)*((9007/50000 : ℝ)+(4507/50000 : ℝ)))^(5727/1024 : ℝ) := by
    rw [show (2499941067857848557/2500000000000000000 : ℝ)+(13359186599/100000000000000 : ℝ)*((9007/50000 : ℝ)+(4507/50000 : ℝ))=(1250015667940849/1250000000000000 : ℝ) by norm_num, show 1+(1716865507106363/25000000000000000000 : ℝ)+(142919225664321/100000000000000000000 : ℝ)=(100007010381254089773/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1716865507106363/25000000000000000000 : ℝ) ≤ ((2499941067857848557/2500000000000000000 : ℝ)+2*(13359186599/100000000000000 : ℝ)*(9007/50000 : ℝ))^(5727/1024 : ℝ) := by
    rw [show (2499941067857848557/2500000000000000000 : ℝ)+2*(13359186599/100000000000000 : ℝ)*(9007/50000 : ℝ)=(10000245576206183/10000000000000000 : ℝ) by norm_num, show 1+2*(1716865507106363/25000000000000000000 : ℝ)=(12501716865507106363/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2499941067857848557/2500000000000000000 : ℝ)*(X 1 0+X 2 0)+(13359186599/100000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (4507/50000 : ℝ)) (hi := (9007/50000 : ℝ)) (c := (2499941067857848557/2500000000000000000 : ℝ)) (alpha := (13359186599/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2499941067857848557/2500000000000000000 : ℝ)*(X 0 1+X 2 1)+(13359186599/100000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (4507/50000 : ℝ)) (hi := (9007/50000 : ℝ)) (c := (2499941067857848557/2500000000000000000 : ℝ)) (alpha := (13359186599/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2499941067857848557/2500000000000000000 : ℝ)*(X 0 2+X 1 2)+(13359186599/100000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (4507/50000 : ℝ)) (hi := (9007/50000 : ℝ)) (c := (2499941067857848557/2500000000000000000 : ℝ)) (alpha := (13359186599/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-168671969/2000000000 : ℝ)*X 0 0+(2713740699/5000000000 : ℝ)*X 0 1+(1356870361/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1298649407/2500000000 : ℝ)*X 1 0+(-294361253/2500000000 : ℝ)*X 1 1+(5427481367/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1038919507/2000000000 : ℝ)*X 2 0+(5427481453/10000000000 : ℝ)*X 2 1+(-588722511/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4551784083/10000000000 : ℝ)*X 0 0+(3801099753/10000000000 : ℝ)*X 0 1+(1900549881/5000000000 : ℝ)*X 0 2+(4551784083/10000000000 : ℝ)*X 1 0+(3801099753/10000000000 : ℝ)*X 1 1+(1900549881/5000000000 : ℝ)*X 1 2+(4551784083/10000000000 : ℝ)*X 2 0+(3801099753/10000000000 : ℝ)*X 2 1+(1900549881/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1663327553/10000000000 : ℝ)*X 0 0+(5128301737/10000000000 : ℝ)*X 0 1+(1282075373/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5395043763/10000000000 : ℝ)*X 1 0+(-656169709/5000000000 : ℝ)*X 1 1+(320518853/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1348760967/2500000000 : ℝ)*X 2 0+(5128301503/10000000000 : ℝ)*X 2 1+(-1312339469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((173103453/500000000 : ℝ)*X 0 0+(2171912661/5000000000 : ℝ)*X 0 1+(2171912581/5000000000 : ℝ)*X 0 2+(173103453/500000000 : ℝ)*X 1 0+(2171912661/5000000000 : ℝ)*X 1 1+(2171912581/5000000000 : ℝ)*X 1 2+(173103453/500000000 : ℝ)*X 2 0+(2171912661/5000000000 : ℝ)*X 2 1+(2171912581/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1485063269/10000000000 : ℝ)*X 0 0+(196028407/400000000 : ℝ)*X 0 1+(5490016563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((644095391/1250000000 : ℝ)*X 1 0+(-1147808967/10000000000 : ℝ)*X 1 1+(5490018997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((103055279/200000000 : ℝ)*X 2 0+(1372504607/2500000000 : ℝ)*X 2 1+(-286952157/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4768957729/10000000000 : ℝ)*X 0 0+(3687231901/10000000000 : ℝ)*X 0 1+(3687231439/10000000000 : ℝ)*X 0 2+(4768957729/10000000000 : ℝ)*X 1 0+(3687231901/10000000000 : ℝ)*X 1 1+(3687231439/10000000000 : ℝ)*X 1 2+(4768957729/10000000000 : ℝ)*X 2 0+(3687231901/10000000000 : ℝ)*X 2 1+(3687231439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-504015941/5000000000 : ℝ)*X 0 0+(5641594381/10000000000 : ℝ)*X 0 1+(2549048057/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5415352849/10000000000 : ℝ)*X 1 0+(-265057459/2000000000 : ℝ)*X 1 1+(5098097057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5415352957/10000000000 : ℝ)*X 2 0+(203923867/400000000 : ℝ)*X 2 1+(-1325287661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((836710543/2500000000 : ℝ)*X 0 0+(4398398013/10000000000 : ℝ)*X 0 1+(4398395809/10000000000 : ℝ)*X 0 2+(836710543/2500000000 : ℝ)*X 1 0+(4398398013/10000000000 : ℝ)*X 1 1+(4398395809/10000000000 : ℝ)*X 1 2+(836710543/2500000000 : ℝ)*X 2 0+(4398398013/10000000000 : ℝ)*X 2 1+(4398395809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-551/800 : ℝ) ≤ (-17218197356608944973469140200051/25000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1620287/12500000000000 : ℝ)*(lower2) + (1320727/20000000000000 : ℝ)*(lower4) + (1794703/20000000000000 : ℝ)*(lower5) + (208558781461781/20000000000000 : ℝ)*(major0) + (208558781461781/20000000000000 : ℝ)*(major1) + (208558781461781/20000000000000 : ℝ)*(major2) + (471968099/100000000000000 : ℝ)*(sp2) + (323765782386039/20000000000000 : ℝ)*(sp4) + (20235362266171/1250000000000 : ℝ)*(sp5) + (404707272416993/25000000000000 : ℝ)*(sp6) + (97943132402143/20000000000000 : ℝ)*(sp7) + (162426469/25000000000000 : ℝ)*(sp8) + (72542799/12500000000000 : ℝ)*(sp13) + (5857703/3125000000000 : ℝ)*(sp15) + (122428962364303/25000000000000 : ℝ)*(f.failure) + (1618829561636071/100000000000000 : ℝ)*(f.sum) + (2255190139819/1000000000000000000000000000 : ℝ)*base65 + (26012406351975017/50000000000000000000000000000000 : ℝ)*base67 + (27670079901975017/50000000000000000000000000000000 : ℝ)*base69 + (310773851998024983/50000000000000000000000000000000 : ℝ)*base72 + (4957616074819/1000000000000000000000000000 : ℝ)*base73 + (226667412898024983/50000000000000000000000000000000 : ℝ)*base76 + (174694197351975017/50000000000000000000000000000000 : ℝ)*base77 + (26162768951975017/50000000000000000000000000000000 : ℝ)*base79 + (2716759824819/1000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (12704749/1250000000000000000000 : ℝ)*base89 + (12704749/1250000000000000000000 : ℝ)*base91 + (12704749/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58013/100000 : ℝ) ≤ (362595039894844306384555269/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3917597/50000000000000 : ℝ)*(lower1) + (2598311/100000000000000 : ℝ)*(lower4) + (3697561/20000000000000 : ℝ)*(lower5) + (145642117248973/12500000000000 : ℝ)*(major0) + (145642117248973/12500000000000 : ℝ)*(major1) + (145642117248973/12500000000000 : ℝ)*(major2) + (1763764477144097/100000000000000 : ℝ)*(sp0) + (176376439590139/10000000000000 : ℝ)*(sp1) + (881882225108327/50000000000000 : ℝ)*(sp2) + (273585209093551/50000000000000 : ℝ)*(sp3) + (112080497/20000000000000 : ℝ)*(sp6) + (45049597/100000000000000 : ℝ)*(sp7) + (2458871/400000000000 : ℝ)*(sp9) + (533475043/100000000000000 : ℝ)*(sp12) + (547170463236699/100000000000000 : ℝ)*(f.failure) + (88188250530957/5000000000000 : ℝ)*(f.sum) + (64605535439/19531250000000000000000000 : ℝ)*base66 + (47440161712206961/31250000000000000000000000000000 : ℝ)*base67 + (143451287631543039/31250000000000000000000000000000 : ℝ)*base70 + (146724500069043039/31250000000000000000000000000000 : ℝ)*base72 + (2597441794077/625000000000000000000000000 : ℝ)*base73 + (95688097319043039/31250000000000000000000000000000 : ℝ)*base76 + (114133782743456961/31250000000000000000000000000000 : ℝ)*base77 + (50514779587206961/31250000000000000000000000000000 : ℝ)*base79 + (856782623601/312500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1816817/5000000000000000000000 : ℝ)*base89 + (1816817/5000000000000000000000 : ℝ)*base91 + (1816817/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (81449/100000 : ℝ) ≤ (2545371503737006618039625678763/3125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7173069/100000000000000 : ℝ)*(lower1) + (45165133/100000000000000 : ℝ)*(lower3) + (112297313/100000000000000 : ℝ)*(upper4) + (56328069581753/5000000000000 : ℝ)*(major0) + (56328069581753/5000000000000 : ℝ)*(major1) + (56328069581753/5000000000000 : ℝ)*(major2) + (1435614947/25000000000000 : ℝ)*(sp0) + (77862292569/100000000000000 : ℝ)*(sp1) + (35682299531/50000000000000 : ℝ)*(sp2) + (19546906123/100000000000000 : ℝ)*(sp3) + (1696911758352327/100000000000000 : ℝ)*(sp8) + (848419819259773/50000000000000 : ℝ)*(sp9) + (424211534053263/25000000000000 : ℝ)*(sp10) + (529035106178683/100000000000000 : ℝ)*(sp11) + (264527326542403/50000000000000 : ℝ)*(f.failure) + (848458750406057/50000000000000 : ℝ)*(f.sum) + (155722795203/250000000000000000000000000 : ℝ)*base66 + (73338744031744579/12500000000000000000000000000000 : ℝ)*base68 + (62740227594244579/12500000000000000000000000000000 : ℝ)*base70 + (76093150094244579/12500000000000000000000000000000 : ℝ)*base72 + (19779769953/250000000000000000000000000 : ℝ)*base74 + (56991617744244579/12500000000000000000000000000000 : ℝ)*base76 + (12806083030755421/12500000000000000000000000000000 : ℝ)*base77 + (12132100194244579/12500000000000000000000000000000 : ℝ)*base80 + (448606357703/250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (16507049/2500000000000000000000 : ℝ)*base89 + (16507049/2500000000000000000000 : ℝ)*base91 + (16507049/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-46431/50000 : ℝ) ≤ (-29018564429773978753699837226259/31250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122177387/100000000000000 : ℝ)*(lower0) + (33571777/100000000000000 : ℝ)*(upper3) + (33361657/100000000000000 : ℝ)*(lower4) + (591023487046671/50000000000000 : ℝ)*(major0) + (591023487046671/50000000000000 : ℝ)*(major1) + (591023487046671/50000000000000 : ℝ)*(major2) + (877079997/20000000000000 : ℝ)*(sp0) + (309369973/12500000000000 : ℝ)*(sp5) + (28686355883/100000000000000 : ℝ)*(sp6) + (4721939/6250000000000 : ℝ)*(sp8) + (1839930884862959/100000000000000 : ℝ)*(sp12) + (229991608856773/12500000000000 : ℝ)*(sp13) + (367981331891617/20000000000000 : ℝ)*(sp14) + (55511173776447/10000000000000 : ℝ)*(sp15) + (55511173776447/10000000000000 : ℝ)*(f.failure) + (114995959113373/6250000000000 : ℝ)*(f.sum) + (30547235209429/2500000000000000000000000000 : ℝ)*base65 + (234648143917771253/125000000000000000000000000000000 : ℝ)*base68 + (824305230042771253/125000000000000000000000000000000 : ℝ)*base70 + (155733539957228747/125000000000000000000000000000000 : ℝ)*base71 + (10735789533071/2500000000000000000000000000 : ℝ)*base74 + (403059022792771253/125000000000000000000000000000000 : ℝ)*base76 + (311039632667771253/125000000000000000000000000000000 : ℝ)*base78 + (228057883292771253/125000000000000000000000000000000 : ℝ)*base80 + (16459366533071/2500000000000000000000000000 : ℝ)*base82 + (4377501/500000000000000000000 : ℝ)*base89 + (4377501/500000000000000000000 : ℝ)*base91 + (4377501/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1748_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (106469283/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4507/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(551/800 : ℝ) ≤ X j i ∧ X j i ≤ -(58013/100000 : ℝ) else (81449/100000 : ℝ) ≤ X j i ∧ X j i ≤ (46431/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1748_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1748_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (106469283/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9013/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(551/800 : ℝ) ≤ X j i ∧ X j i ≤ -(58013/100000 : ℝ) else (81449/100000 : ℝ) ≤ X j i ∧ X j i ≤ (46431/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1748_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1748_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (106469283/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9013/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(551/800 : ℝ) ≤ X j i ∧ X j i ≤ -(58013/100000 : ℝ) else (81449/100000 : ℝ) ≤ X j i ∧ X j i ≤ (46431/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1748_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
