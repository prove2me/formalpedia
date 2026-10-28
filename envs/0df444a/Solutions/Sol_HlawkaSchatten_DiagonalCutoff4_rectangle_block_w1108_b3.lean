-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1108_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:04:08.762911+00:00
-- url     : https://prove2.me/submissions/1779fd7a-1d5e-4564-a4df-1d51af4e7e0f

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
theorem support_rectangle_w1108_s9_0 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344860379/10000000000 : ℝ)*x 0 + (5265225157/10000000000 : ℝ)*x 1 + (-89934833/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344860379/10000000000 : ℝ)^8301 ≤ (43534075313971/100000000000000 : ℝ)^6253 := by
    have hnat : (5344860379 : ℕ)^8301*100000000000000^6253 ≤ 43534075313971^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344860379 10000000000 43534075313971 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265225157/10000000000 : ℝ)^8301 ≤ (1066877750371/2500000000000 : ℝ)^6253 := by
    have hnat : (5265225157 : ℕ)^8301*2500000000000^6253 ≤ 1066877750371^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265225157 10000000000 1066877750371 2500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89934833/400000000 : ℝ)^8301 ≤ (13790814653481/100000000000000 : ℝ)^6253 := by
    have hnat : (89934833 : ℕ)^8301*100000000000000^6253 ≤ 13790814653481^6253*400000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89934833 400000000 13790814653481 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344860379/10000000000 : ℝ), (5265225157/10000000000 : ℝ), (-89934833/400000000 : ℝ)] ![(43534075313971/100000000000000 : ℝ), (1066877750371/2500000000000 : ℝ), (13790814653481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344860379/10000000000 : ℝ)|^8301 ≤ (43534075313971/100000000000000 : ℝ)^6253
        have hw : |(5344860379/10000000000 : ℝ)|=(5344860379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265225157/10000000000 : ℝ)|^8301 ≤ (1066877750371/2500000000000 : ℝ)^6253
        have hw : |(5265225157/10000000000 : ℝ)|=(5265225157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-89934833/400000000 : ℝ)|^8301 ≤ (13790814653481/100000000000000 : ℝ)^6253
        have hw : |(-89934833/400000000 : ℝ)|=(89934833/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s9_1 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369487719/10000000000 : ℝ)*x 0 + (1061123807/2500000000 : ℝ)*x 1 + (4498173421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369487719/10000000000 : ℝ)^8301 ≤ (33316803322811/100000000000000 : ℝ)^6253 := by
    have hnat : (4369487719 : ℕ)^8301*100000000000000^6253 ≤ 33316803322811^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369487719 10000000000 33316803322811 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061123807/2500000000 : ℝ)^8301 ≤ (32057570011911/100000000000000 : ℝ)^6253 := by
    have hnat : (1061123807 : ℕ)^8301*100000000000000^6253 ≤ 32057570011911^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061123807 2500000000 32057570011911 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498173421/10000000000 : ℝ)^8301 ≤ (6925125330231/20000000000000 : ℝ)^6253 := by
    have hnat : (4498173421 : ℕ)^8301*20000000000000^6253 ≤ 6925125330231^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498173421 10000000000 6925125330231 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369487719/10000000000 : ℝ), (1061123807/2500000000 : ℝ), (4498173421/10000000000 : ℝ)] ![(33316803322811/100000000000000 : ℝ), (32057570011911/100000000000000 : ℝ), (6925125330231/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369487719/10000000000 : ℝ)|^8301 ≤ (33316803322811/100000000000000 : ℝ)^6253
        have hw : |(4369487719/10000000000 : ℝ)|=(4369487719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061123807/2500000000 : ℝ)|^8301 ≤ (32057570011911/100000000000000 : ℝ)^6253
        have hw : |(1061123807/2500000000 : ℝ)|=(1061123807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498173421/10000000000 : ℝ)|^8301 ≤ (6925125330231/20000000000000 : ℝ)^6253
        have hw : |(4498173421/10000000000 : ℝ)|=(4498173421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s9_2 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183258587/10000000000 : ℝ)*x 0 + (2632773677/5000000000 : ℝ)*x 1 + (26966337/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183258587/10000000000 : ℝ)^8301 ≤ (1657895200343/12500000000000 : ℝ)^6253 := by
    have hnat : (2183258587 : ℕ)^8301*12500000000000^6253 ≤ 1657895200343^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183258587 10000000000 1657895200343 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632773677/5000000000 : ℝ)^8301 ≤ (10669644197211/25000000000000 : ℝ)^6253 := by
    have hnat : (2632773677 : ℕ)^8301*25000000000000^6253 ≤ 10669644197211^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632773677 5000000000 10669644197211 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26966337/50000000 : ℝ)^8301 ≤ (44058261588251/100000000000000 : ℝ)^6253 := by
    have hnat : (26966337 : ℕ)^8301*100000000000000^6253 ≤ 44058261588251^6253*50000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26966337 50000000 44058261588251 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183258587/10000000000 : ℝ), (2632773677/5000000000 : ℝ), (26966337/50000000 : ℝ)] ![(1657895200343/12500000000000 : ℝ), (10669644197211/25000000000000 : ℝ), (44058261588251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183258587/10000000000 : ℝ)|^8301 ≤ (1657895200343/12500000000000 : ℝ)^6253
        have hw : |(-2183258587/10000000000 : ℝ)|=(2183258587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632773677/5000000000 : ℝ)|^8301 ≤ (10669644197211/25000000000000 : ℝ)^6253
        have hw : |(2632773677/5000000000 : ℝ)|=(2632773677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26966337/50000000 : ℝ)|^8301 ≤ (44058261588251/100000000000000 : ℝ)^6253
        have hw : |(26966337/50000000 : ℝ)|=(26966337/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s9_3 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332026307/625000000 : ℝ)*x 0 + (-1060164003/5000000000 : ℝ)*x 1 + (5393268429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332026307/625000000 : ℝ)^8301 ≤ (4318366554999/10000000000000 : ℝ)^6253 := by
    have hnat : (332026307 : ℕ)^8301*10000000000000^6253 ≤ 4318366554999^6253*625000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332026307 625000000 4318366554999 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060164003/5000000000 : ℝ)^8301 ≤ (1594757711351/12500000000000 : ℝ)^6253 := by
    have hnat : (1060164003 : ℕ)^8301*12500000000000^6253 ≤ 1594757711351^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060164003 5000000000 1594757711351 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393268429/10000000000 : ℝ)^8301 ≤ (11014568186861/25000000000000 : ℝ)^6253 := by
    have hnat : (5393268429 : ℕ)^8301*25000000000000^6253 ≤ 11014568186861^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393268429 10000000000 11014568186861 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332026307/625000000 : ℝ), (-1060164003/5000000000 : ℝ), (5393268429/10000000000 : ℝ)] ![(4318366554999/10000000000000 : ℝ), (1594757711351/12500000000000 : ℝ), (11014568186861/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332026307/625000000 : ℝ)|^8301 ≤ (4318366554999/10000000000000 : ℝ)^6253
        have hw : |(332026307/625000000 : ℝ)|=(332026307/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1060164003/5000000000 : ℝ)|^8301 ≤ (1594757711351/12500000000000 : ℝ)^6253
        have hw : |(-1060164003/5000000000 : ℝ)|=(1060164003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393268429/10000000000 : ℝ)|^8301 ≤ (11014568186861/25000000000000 : ℝ)^6253
        have hw : |(5393268429/10000000000 : ℝ)|=(5393268429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s9_4 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531242169/1000000000 : ℝ)*x 0 + (5393267567/10000000000 : ℝ)*x 1 + (-135701/640000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531242169/1000000000 : ℝ)^8301 ≤ (4318367394553/10000000000000 : ℝ)^6253 := by
    have hnat : (531242169 : ℕ)^8301*10000000000000^6253 ≤ 4318367394553^6253*1000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531242169 1000000000 4318367394553 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393267567/10000000000 : ℝ)^8301 ≤ (8811652679863/20000000000000 : ℝ)^6253 := by
    have hnat : (5393267567 : ℕ)^8301*20000000000000^6253 ≤ 8811652679863^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393267567 10000000000 8811652679863 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135701/640000 : ℝ)^8301 ≤ (12758062641349/100000000000000 : ℝ)^6253 := by
    have hnat : (135701 : ℕ)^8301*100000000000000^6253 ≤ 12758062641349^6253*640000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135701 640000 12758062641349 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531242169/1000000000 : ℝ), (5393267567/10000000000 : ℝ), (-135701/640000 : ℝ)] ![(4318367394553/10000000000000 : ℝ), (8811652679863/20000000000000 : ℝ), (12758062641349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531242169/1000000000 : ℝ)|^8301 ≤ (4318367394553/10000000000000 : ℝ)^6253
        have hw : |(531242169/1000000000 : ℝ)|=(531242169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393267567/10000000000 : ℝ)|^8301 ≤ (8811652679863/20000000000000 : ℝ)^6253
        have hw : |(5393267567/10000000000 : ℝ)|=(5393267567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-135701/640000 : ℝ)|^8301 ≤ (12758062641349/100000000000000 : ℝ)^6253
        have hw : |(-135701/640000 : ℝ)|=(135701/640000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s9_5 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184748561/5000000000 : ℝ)*x 0 + (4497537579/10000000000 : ℝ)*x 1 + (4245133751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184748561/5000000000 : ℝ)^8301 ≤ (4164612312733/12500000000000 : ℝ)^6253 := by
    have hnat : (2184748561 : ℕ)^8301*12500000000000^6253 ≤ 4164612312733^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184748561 5000000000 4164612312733 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497537579/10000000000 : ℝ)^8301 ≤ (17309564603243/50000000000000 : ℝ)^6253 := by
    have hnat : (4497537579 : ℕ)^8301*50000000000000^6253 ≤ 17309564603243^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497537579 10000000000 17309564603243 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4245133751/10000000000 : ℝ)^8301 ≤ (32063972278867/100000000000000 : ℝ)^6253 := by
    have hnat : (4245133751 : ℕ)^8301*100000000000000^6253 ≤ 32063972278867^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245133751 10000000000 32063972278867 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184748561/5000000000 : ℝ), (4497537579/10000000000 : ℝ), (4245133751/10000000000 : ℝ)] ![(4164612312733/12500000000000 : ℝ), (17309564603243/50000000000000 : ℝ), (32063972278867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184748561/5000000000 : ℝ)|^8301 ≤ (4164612312733/12500000000000 : ℝ)^6253
        have hw : |(2184748561/5000000000 : ℝ)|=(2184748561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497537579/10000000000 : ℝ)|^8301 ≤ (17309564603243/50000000000000 : ℝ)^6253
        have hw : |(4497537579/10000000000 : ℝ)|=(4497537579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4245133751/10000000000 : ℝ)|^8301 ≤ (32063972278867/100000000000000 : ℝ)^6253
        have hw : |(4245133751/10000000000 : ℝ)|=(4245133751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1108_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11309/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3507/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11309/100000 : ℝ) ^ (2075/512 : ℝ) ≤ (1822593202880701/12500000000000000000 : ℝ) := by
    have hpowers : (11309/100000 : ℝ)^2075 ≤ (1822593202880701/12500000000000000000 : ℝ)^512 := by
      have hnat : (11309 : ℕ)^2075*12500000000000000000^512 ≤ 1822593202880701^512*100000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11309 100000 1822593202880701 12500000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11309/100000 : ℝ)) (X := (1822593202880701/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14029/100000 : ℝ) ^ (2075/512 : ℝ) ≤ (34924150238686577/100000000000000000000 : ℝ) := by
    have hpowers : (14029/100000 : ℝ)^2075 ≤ (34924150238686577/100000000000000000000 : ℝ)^512 := by
      have hnat : (14029 : ℕ)^2075*100000000000000000000^512 ≤ 34924150238686577^512*100000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14029 100000 34924150238686577 100000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14029/100000 : ℝ)) (X := (34924150238686577/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251822593202880701/6250000000000000000 : ℝ) ≤ (5000359735999081/5000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (6251822593202880701/6250000000000000000 : ℝ)^512 ≤ (5000359735999081/5000000000000000 : ℝ)^2075 := by
      have hnat : (6251822593202880701 : ℕ)^512*5000000000000000^2075 ≤ 5000359735999081^2075*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251822593202880701 6250000000000000000 5000359735999081 5000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000359735999081/5000000000000000 : ℝ)) (X := (6251822593202880701/6250000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009900979172346437/20000000000000000000 : ℝ) ≤ (50006106453549/50000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (20009900979172346437/20000000000000000000 : ℝ)^512 ≤ (50006106453549/50000000000000 : ℝ)^2075 := by
      have hnat : (20009900979172346437 : ℕ)^512*50000000000000^2075 ≤ 50006106453549^2075*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009900979172346437 20000000000000000000 50006106453549 50000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50006106453549/50000000000000 : ℝ)) (X := (20009900979172346437/20000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034924150238686577/50000000000000000000 : ℝ) ≤ (5000861554710719/5000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (50034924150238686577/50000000000000000000 : ℝ)^512 ≤ (5000861554710719/5000000000000000 : ℝ)^2075 := by
      have hnat : (50034924150238686577 : ℕ)^512*5000000000000000^2075 ≤ 5000861554710719^2075*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034924150238686577 50000000000000000000 5000861554710719 5000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000861554710719/5000000000000000 : ℝ)) (X := (50034924150238686577/50000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1822593202880701/12500000000000000000 : ℝ) ≤ ((6797651707053793089/6800000000000000000 : ℝ)+2*(250909355819/136000000000000 : ℝ)*(11309/100000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (6797651707053793089/6800000000000000000 : ℝ)+2*(250909355819/136000000000000 : ℝ)*(11309/100000 : ℝ)=(5000359735999081/5000000000000000 : ℝ) by norm_num, show 1+2*(1822593202880701/12500000000000000000 : ℝ)=(6251822593202880701/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34924150238686577/100000000000000000000 : ℝ)+(1822593202880701/12500000000000000000 : ℝ) ≤ ((6797651707053793089/6800000000000000000 : ℝ)+(250909355819/136000000000000 : ℝ)*((14029/100000 : ℝ)+(11309/100000 : ℝ)))^(2075/512 : ℝ) := by
    rw [show (6797651707053793089/6800000000000000000 : ℝ)+(250909355819/136000000000000 : ℝ)*((14029/100000 : ℝ)+(11309/100000 : ℝ))=(50006106453549/50000000000000 : ℝ) by norm_num, show 1+(34924150238686577/100000000000000000000 : ℝ)+(1822593202880701/12500000000000000000 : ℝ)=(20009900979172346437/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34924150238686577/100000000000000000000 : ℝ) ≤ ((6797651707053793089/6800000000000000000 : ℝ)+2*(250909355819/136000000000000 : ℝ)*(14029/100000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (6797651707053793089/6800000000000000000 : ℝ)+2*(250909355819/136000000000000 : ℝ)*(14029/100000 : ℝ)=(5000861554710719/5000000000000000 : ℝ) by norm_num, show 1+2*(34924150238686577/100000000000000000000 : ℝ)=(50034924150238686577/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6797651707053793089/6800000000000000000 : ℝ)*(X 1 0+X 2 0)+(250909355819/136000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (6797651707053793089/6800000000000000000 : ℝ)) (alpha := (250909355819/136000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6797651707053793089/6800000000000000000 : ℝ)*(X 0 1+X 2 1)+(250909355819/136000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (6797651707053793089/6800000000000000000 : ℝ)) (alpha := (250909355819/136000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6797651707053793089/6800000000000000000 : ℝ)*(X 0 2+X 1 2)+(250909355819/136000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (6797651707053793089/6800000000000000000 : ℝ)) (alpha := (250909355819/136000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5344860379/10000000000 : ℝ)*X 2 0+(5265225157/10000000000 : ℝ)*X 2 1+(-89934833/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((4369487719/10000000000 : ℝ)*X 0 0+(1061123807/2500000000 : ℝ)*X 0 1+(4498173421/10000000000 : ℝ)*X 0 2+(4369487719/10000000000 : ℝ)*X 1 0+(1061123807/2500000000 : ℝ)*X 1 1+(4498173421/10000000000 : ℝ)*X 1 2+(4369487719/10000000000 : ℝ)*X 2 0+(1061123807/2500000000 : ℝ)*X 2 1+(4498173421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s9_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-2183258587/10000000000 : ℝ)*X 0 0+(2632773677/5000000000 : ℝ)*X 0 1+(26966337/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((332026307/625000000 : ℝ)*X 1 0+(-1060164003/5000000000 : ℝ)*X 1 1+(5393268429/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((531242169/1000000000 : ℝ)*X 2 0+(5393267567/10000000000 : ℝ)*X 2 1+(-135701/640000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2184748561/5000000000 : ℝ)*X 0 0+(4497537579/10000000000 : ℝ)*X 0 1+(4245133751/10000000000 : ℝ)*X 0 2+(2184748561/5000000000 : ℝ)*X 1 0+(4497537579/10000000000 : ℝ)*X 1 1+(4245133751/10000000000 : ℝ)*X 1 2+(2184748561/5000000000 : ℝ)*X 2 0+(4497537579/10000000000 : ℝ)*X 2 1+(4245133751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54077902977990123325661601/10000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62577517/5000000000000 : ℝ)*(base23) + (64900757/10000000000000 : ℝ)*(lower1) + (13477933/12500000000000 : ℝ)*(upper2) + (31331183/20000000000000 : ℝ)*(upper3) + (77971637/100000000000000 : ℝ)*(upper4) + (5895741227948851/100000000000000 : ℝ)*(major0) + (5895741227948851/100000000000000 : ℝ)*(major1) + (5895741227948851/100000000000000 : ℝ)*(major2) + (1595834463/20000000000000 : ℝ)*(sp0) + (1050556059/12500000000000 : ℝ)*(sp1) + (7829577109418987/100000000000000 : ℝ)*(sp2) + (7829577109418987/100000000000000 : ℝ)*(sp3) + (1957391969674083/25000000000000 : ℝ)*(sp4) + (3961896761770557/100000000000000 : ℝ)*(sp5) + (990476291554757/25000000000000 : ℝ)*(f.failure) + (7829577109418987/100000000000000 : ℝ)*(f.sum) + (517760192143/400000000000000000000000000 : ℝ)*base66 + (187434703060721133/40000000000000000000000000000000 : ℝ)*base68 + (595386395140721133/40000000000000000000000000000000 : ℝ)*base70 + (295216501020721133/40000000000000000000000000000000 : ℝ)*base72 + (387897089743/400000000000000000000000000 : ℝ)*base74 + (419071900060721133/40000000000000000000000000000000 : ℝ)*base76 + (585231806139278867/40000000000000000000000000000000 : ℝ)*base77 + (472161995100721133/40000000000000000000000000000000 : ℝ)*base80 + (1048169668543/400000000000000000000000000 : ℝ)*base82 + (12659923/2500000000000000000000 : ℝ)*base90 + (12659923/2500000000000000000000 : ℝ)*base92 + (12659923/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1108_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1108_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1108_box_0 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1027615757/5000000000 : ℝ)*x 0 + (5376788281/10000000000 : ℝ)*x 1 + (1344197053/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027615757/5000000000 : ℝ)^8301 ≤ (3060180164551/25000000000000 : ℝ)^6253 := by
    have hnat : (1027615757 : ℕ)^8301*25000000000000^6253 ≤ 3060180164551^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027615757 5000000000 3060180164551 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376788281/10000000000 : ℝ)^8301 ≤ (171404843879/390625000000 : ℝ)^6253 := by
    have hnat : (5376788281 : ℕ)^8301*390625000000^6253 ≤ 171404843879^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376788281 10000000000 171404843879 390625000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344197053/2500000000 : ℝ)^8301 ≤ (4387963928549/10000000000000 : ℝ)^6253 := by
    have hnat : (1344197053 : ℕ)^8301*10000000000000^6253 ≤ 4387963928549^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344197053 2500000000 4387963928549 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1027615757/5000000000 : ℝ), (5376788281/10000000000 : ℝ), (1344197053/2500000000 : ℝ)] ![(3060180164551/25000000000000 : ℝ), (171404843879/390625000000 : ℝ), (4387963928549/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1027615757/5000000000 : ℝ)|^8301 ≤ (3060180164551/25000000000000 : ℝ)^6253
        have hw : |(-1027615757/5000000000 : ℝ)|=(1027615757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376788281/10000000000 : ℝ)|^8301 ≤ (171404843879/390625000000 : ℝ)^6253
        have hw : |(5376788281/10000000000 : ℝ)|=(5376788281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344197053/2500000000 : ℝ)|^8301 ≤ (4387963928549/10000000000000 : ℝ)^6253
        have hw : |(1344197053/2500000000 : ℝ)|=(1344197053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_1 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1323913449/2500000000 : ℝ)*x 0 + (-135323551/625000000 : ℝ)*x 1 + (2688394171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323913449/2500000000 : ℝ)^8301 ≤ (43002822138427/100000000000000 : ℝ)^6253 := by
    have hnat : (1323913449 : ℕ)^8301*100000000000000^6253 ≤ 43002822138427^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323913449 2500000000 43002822138427 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135323551/625000000 : ℝ)^8301 ≤ (3279384286901/25000000000000 : ℝ)^6253 := by
    have hnat : (135323551 : ℕ)^8301*25000000000000^6253 ≤ 3279384286901^6253*625000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135323551 625000000 3279384286901 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688394171/5000000000 : ℝ)^8301 ≤ (342809692921/781250000000 : ℝ)^6253 := by
    have hnat : (2688394171 : ℕ)^8301*781250000000^6253 ≤ 342809692921^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688394171 5000000000 342809692921 781250000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323913449/2500000000 : ℝ), (-135323551/625000000 : ℝ), (2688394171/5000000000 : ℝ)] ![(43002822138427/100000000000000 : ℝ), (3279384286901/25000000000000 : ℝ), (342809692921/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323913449/2500000000 : ℝ)|^8301 ≤ (43002822138427/100000000000000 : ℝ)^6253
        have hw : |(1323913449/2500000000 : ℝ)|=(1323913449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135323551/625000000 : ℝ)|^8301 ≤ (3279384286901/25000000000000 : ℝ)^6253
        have hw : |(-135323551/625000000 : ℝ)|=(135323551/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688394171/5000000000 : ℝ)|^8301 ≤ (342809692921/781250000000 : ℝ)^6253
        have hw : |(2688394171/5000000000 : ℝ)|=(2688394171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_2 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295653873/10000000000 : ℝ)*x 0 + (2688394053/5000000000 : ℝ)*x 1 + (-2165177031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295653873/10000000000 : ℝ)^8301 ≤ (5375352871061/12500000000000 : ℝ)^6253 := by
    have hnat : (5295653873 : ℕ)^8301*12500000000000^6253 ≤ 5375352871061^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295653873 10000000000 5375352871061 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688394053/5000000000 : ℝ)^8301 ≤ (43879638137103/100000000000000 : ℝ)^6253 := by
    have hnat : (2688394053 : ℕ)^8301*100000000000000^6253 ≤ 43879638137103^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688394053 5000000000 43879638137103 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2165177031/10000000000 : ℝ)^8301 ≤ (13117538876781/100000000000000 : ℝ)^6253 := by
    have hnat : (2165177031 : ℕ)^8301*100000000000000^6253 ≤ 13117538876781^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165177031 10000000000 13117538876781 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295653873/10000000000 : ℝ), (2688394053/5000000000 : ℝ), (-2165177031/10000000000 : ℝ)] ![(5375352871061/12500000000000 : ℝ), (43879638137103/100000000000000 : ℝ), (13117538876781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295653873/10000000000 : ℝ)|^8301 ≤ (5375352871061/12500000000000 : ℝ)^6253
        have hw : |(5295653873/10000000000 : ℝ)|=(5295653873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688394053/5000000000 : ℝ)|^8301 ≤ (43879638137103/100000000000000 : ℝ)^6253
        have hw : |(2688394053/5000000000 : ℝ)|=(2688394053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2165177031/10000000000 : ℝ)|^8301 ≤ (13117538876781/100000000000000 : ℝ)^6253
        have hw : |(-2165177031/10000000000 : ℝ)|=(2165177031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_3 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (895479881/2000000000 : ℝ)*x 0 + (4317663217/10000000000 : ℝ)*x 1 + (134926993/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (895479881/2000000000 : ℝ)^8301 ≤ (6882700025923/20000000000000 : ℝ)^6253 := by
    have hnat : (895479881 : ℕ)^8301*20000000000000^6253 ≤ 6882700025923^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895479881 2000000000 6882700025923 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4317663217/10000000000 : ℝ)^8301 ≤ (3279324711139/10000000000000 : ℝ)^6253 := by
    have hnat : (4317663217 : ℕ)^8301*10000000000000^6253 ≤ 3279324711139^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317663217 10000000000 3279324711139 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134926993/312500000 : ℝ)^8301 ≤ (3279325274763/10000000000000 : ℝ)^6253 := by
    have hnat : (134926993 : ℕ)^8301*10000000000000^6253 ≤ 3279325274763^6253*312500000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134926993 312500000 3279325274763 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(895479881/2000000000 : ℝ), (4317663217/10000000000 : ℝ), (134926993/312500000 : ℝ)] ![(6882700025923/20000000000000 : ℝ), (3279324711139/10000000000000 : ℝ), (3279325274763/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(895479881/2000000000 : ℝ)|^8301 ≤ (6882700025923/20000000000000 : ℝ)^6253
        have hw : |(895479881/2000000000 : ℝ)|=(895479881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4317663217/10000000000 : ℝ)|^8301 ≤ (3279324711139/10000000000000 : ℝ)^6253
        have hw : |(4317663217/10000000000 : ℝ)|=(4317663217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134926993/312500000 : ℝ)|^8301 ≤ (3279325274763/10000000000000 : ℝ)^6253
        have hw : |(134926993/312500000 : ℝ)|=(134926993/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_4 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-578166793/2500000000 : ℝ)*x 0 + (1056138341/2000000000 : ℝ)*x 1 + (528069153/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (578166793/2500000000 : ℝ)^8301 ≤ (14316791372019/100000000000000 : ℝ)^6253 := by
    have hnat : (578166793 : ℕ)^8301*100000000000000^6253 ≤ 14316791372019^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578166793 2500000000 14316791372019 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056138341/2000000000 : ℝ)^8301 ≤ (42841605250067/100000000000000 : ℝ)^6253 := by
    have hnat : (1056138341 : ℕ)^8301*100000000000000^6253 ≤ 42841605250067^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056138341 2000000000 42841605250067 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528069153/1000000000 : ℝ)^8301 ≤ (669400052583/1562500000000 : ℝ)^6253 := by
    have hnat : (528069153 : ℕ)^8301*1562500000000^6253 ≤ 669400052583^6253*1000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528069153 1000000000 669400052583 1562500000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-578166793/2500000000 : ℝ), (1056138341/2000000000 : ℝ), (528069153/1000000000 : ℝ)] ![(14316791372019/100000000000000 : ℝ), (42841605250067/100000000000000 : ℝ), (669400052583/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-578166793/2500000000 : ℝ)|^8301 ≤ (14316791372019/100000000000000 : ℝ)^6253
        have hw : |(-578166793/2500000000 : ℝ)|=(578166793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056138341/2000000000 : ℝ)|^8301 ≤ (42841605250067/100000000000000 : ℝ)^6253
        have hw : |(1056138341/2000000000 : ℝ)|=(1056138341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528069153/1000000000 : ℝ)|^8301 ≤ (669400052583/1562500000000 : ℝ)^6253
        have hw : |(528069153/1000000000 : ℝ)|=(528069153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_5 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363598247/10000000000 : ℝ)*x 0 + (-2202875511/10000000000 : ℝ)*x 1 + (2640345803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363598247/10000000000 : ℝ)^8301 ≤ (43736798855983/100000000000000 : ℝ)^6253 := by
    have hnat : (5363598247 : ℕ)^8301*100000000000000^6253 ≤ 43736798855983^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363598247 10000000000 43736798855983 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2202875511/10000000000 : ℝ)^8301 ≤ (13421596942467/100000000000000 : ℝ)^6253 := by
    have hnat : (2202875511 : ℕ)^8301*100000000000000^6253 ≤ 13421596942467^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202875511 10000000000 13421596942467 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640345803/5000000000 : ℝ)^8301 ≤ (21420802091917/50000000000000 : ℝ)^6253 := by
    have hnat : (2640345803 : ℕ)^8301*50000000000000^6253 ≤ 21420802091917^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640345803 5000000000 21420802091917 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363598247/10000000000 : ℝ), (-2202875511/10000000000 : ℝ), (2640345803/5000000000 : ℝ)] ![(43736798855983/100000000000000 : ℝ), (13421596942467/100000000000000 : ℝ), (21420802091917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363598247/10000000000 : ℝ)|^8301 ≤ (43736798855983/100000000000000 : ℝ)^6253
        have hw : |(5363598247/10000000000 : ℝ)|=(5363598247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2202875511/10000000000 : ℝ)|^8301 ≤ (13421596942467/100000000000000 : ℝ)^6253
        have hw : |(-2202875511/10000000000 : ℝ)|=(2202875511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640345803/5000000000 : ℝ)|^8301 ≤ (21420802091917/50000000000000 : ℝ)^6253
        have hw : |(2640345803/5000000000 : ℝ)|=(2640345803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_6 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681799129/5000000000 : ℝ)*x 0 + (2640345753/5000000000 : ℝ)*x 1 + (-2202875631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681799129/5000000000 : ℝ)^8301 ≤ (43736798975059/100000000000000 : ℝ)^6253 := by
    have hnat : (2681799129 : ℕ)^8301*100000000000000^6253 ≤ 43736798975059^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681799129 5000000000 43736798975059 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640345753/5000000000 : ℝ)^8301 ≤ (42841603106831/100000000000000 : ℝ)^6253 := by
    have hnat : (2640345753 : ℕ)^8301*100000000000000^6253 ≤ 42841603106831^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640345753 5000000000 42841603106831 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202875631/10000000000 : ℝ)^8301 ≤ (13421597913061/100000000000000 : ℝ)^6253 := by
    have hnat : (2202875631 : ℕ)^8301*100000000000000^6253 ≤ 13421597913061^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202875631 10000000000 13421597913061 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681799129/5000000000 : ℝ), (2640345753/5000000000 : ℝ), (-2202875631/10000000000 : ℝ)] ![(43736798975059/100000000000000 : ℝ), (42841603106831/100000000000000 : ℝ), (13421597913061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681799129/5000000000 : ℝ)|^8301 ≤ (43736798975059/100000000000000 : ℝ)^6253
        have hw : |(2681799129/5000000000 : ℝ)|=(2681799129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640345753/5000000000 : ℝ)|^8301 ≤ (42841603106831/100000000000000 : ℝ)^6253
        have hw : |(2640345753/5000000000 : ℝ)|=(2640345753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2202875631/10000000000 : ℝ)|^8301 ≤ (13421597913061/100000000000000 : ℝ)^6253
        have hw : |(-2202875631/10000000000 : ℝ)|=(2202875631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_7 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (852245789/2000000000 : ℝ)*x 0 + (553215981/1250000000 : ℝ)*x 1 + (4425727387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852245789/2000000000 : ℝ)^8301 ≤ (8056364440301/25000000000000 : ℝ)^6253 := by
    have hnat : (852245789 : ℕ)^8301*25000000000000^6253 ≤ 8056364440301^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852245789 2000000000 8056364440301 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553215981/1250000000 : ℝ)^8301 ≤ (2117954591007/6250000000000 : ℝ)^6253 := by
    have hnat : (553215981 : ℕ)^8301*6250000000000^6253 ≤ 2117954591007^6253*1250000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553215981 1250000000 2117954591007 6250000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4425727387/10000000000 : ℝ)^8301 ≤ (2117954298137/6250000000000 : ℝ)^6253 := by
    have hnat : (4425727387 : ℕ)^8301*6250000000000^6253 ≤ 2117954298137^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4425727387 10000000000 2117954298137 6250000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852245789/2000000000 : ℝ), (553215981/1250000000 : ℝ), (4425727387/10000000000 : ℝ)] ![(8056364440301/25000000000000 : ℝ), (2117954591007/6250000000000 : ℝ), (2117954298137/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852245789/2000000000 : ℝ)|^8301 ≤ (8056364440301/25000000000000 : ℝ)^6253
        have hw : |(852245789/2000000000 : ℝ)|=(852245789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(553215981/1250000000 : ℝ)|^8301 ≤ (2117954591007/6250000000000 : ℝ)^6253
        have hw : |(553215981/1250000000 : ℝ)|=(553215981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4425727387/10000000000 : ℝ)|^8301 ≤ (2117954298137/6250000000000 : ℝ)^6253
        have hw : |(4425727387/10000000000 : ℝ)|=(4425727387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_8 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1129436797/5000000000 : ℝ)*x 0 + (1303850619/2500000000 : ℝ)*x 1 + (5386393701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1129436797/5000000000 : ℝ)^8301 ≤ (277528000459/2000000000000 : ℝ)^6253 := by
    have hnat : (1129436797 : ℕ)^8301*2000000000000^6253 ≤ 277528000459^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129436797 5000000000 277528000459 2000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303850619/2500000000 : ℝ)^8301 ≤ (10534966494603/25000000000000 : ℝ)^6253 := by
    have hnat : (1303850619 : ℕ)^8301*25000000000000^6253 ≤ 10534966494603^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303850619 2500000000 10534966494603 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386393701/10000000000 : ℝ)^8301 ≤ (8796746794729/20000000000000 : ℝ)^6253 := by
    have hnat : (5386393701 : ℕ)^8301*20000000000000^6253 ≤ 8796746794729^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386393701 10000000000 8796746794729 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1129436797/5000000000 : ℝ), (1303850619/2500000000 : ℝ), (5386393701/10000000000 : ℝ)] ![(277528000459/2000000000000 : ℝ), (10534966494603/25000000000000 : ℝ), (8796746794729/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1129436797/5000000000 : ℝ)|^8301 ≤ (277528000459/2000000000000 : ℝ)^6253
        have hw : |(-1129436797/5000000000 : ℝ)|=(1129436797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303850619/2500000000 : ℝ)|^8301 ≤ (10534966494603/25000000000000 : ℝ)^6253
        have hw : |(1303850619/2500000000 : ℝ)|=(1303850619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386393701/10000000000 : ℝ)|^8301 ≤ (8796746794729/20000000000000 : ℝ)^6253
        have hw : |(5386393701/10000000000 : ℝ)|=(5386393701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_9 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644429429/5000000000 : ℝ)*x 0 + (-2161338961/10000000000 : ℝ)*x 1 + (5386393567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644429429/5000000000 : ℝ)^8301 ≤ (42929588002089/100000000000000 : ℝ)^6253 := by
    have hnat : (2644429429 : ℕ)^8301*100000000000000^6253 ≤ 42929588002089^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644429429 5000000000 42929588002089 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2161338961/10000000000 : ℝ)^8301 ≤ (13086679462009/100000000000000 : ℝ)^6253 := by
    have hnat : (2161338961 : ℕ)^8301*100000000000000^6253 ≤ 13086679462009^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161338961 10000000000 13086679462009 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386393567/10000000000 : ℝ)^8301 ≤ (43983732521063/100000000000000 : ℝ)^6253 := by
    have hnat : (5386393567 : ℕ)^8301*100000000000000^6253 ≤ 43983732521063^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386393567 10000000000 43983732521063 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644429429/5000000000 : ℝ), (-2161338961/10000000000 : ℝ), (5386393567/10000000000 : ℝ)] ![(42929588002089/100000000000000 : ℝ), (13086679462009/100000000000000 : ℝ), (43983732521063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644429429/5000000000 : ℝ)|^8301 ≤ (42929588002089/100000000000000 : ℝ)^6253
        have hw : |(2644429429/5000000000 : ℝ)|=(2644429429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2161338961/10000000000 : ℝ)|^8301 ≤ (13086679462009/100000000000000 : ℝ)^6253
        have hw : |(-2161338961/10000000000 : ℝ)|=(2161338961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386393567/10000000000 : ℝ)|^8301 ≤ (43983732521063/100000000000000 : ℝ)^6253
        have hw : |(5386393567/10000000000 : ℝ)|=(5386393567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_10 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288858971/10000000000 : ℝ)*x 0 + (538639369/1000000000 : ℝ)*x 1 + (-2161338643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288858971/10000000000 : ℝ)^8301 ≤ (21464794609859/50000000000000 : ℝ)^6253 := by
    have hnat : (5288858971 : ℕ)^8301*50000000000000^6253 ≤ 21464794609859^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288858971 10000000000 21464794609859 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538639369/1000000000 : ℝ)^8301 ≤ (43983733854403/100000000000000 : ℝ)^6253 := by
    have hnat : (538639369 : ℕ)^8301*100000000000000^6253 ≤ 43983733854403^6253*1000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538639369 1000000000 43983733854403 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161338643/10000000000 : ℝ)^8301 ≤ (6543338452961/50000000000000 : ℝ)^6253 := by
    have hnat : (2161338643 : ℕ)^8301*50000000000000^6253 ≤ 6543338452961^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161338643 10000000000 6543338452961 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288858971/10000000000 : ℝ), (538639369/1000000000 : ℝ), (-2161338643/10000000000 : ℝ)] ![(21464794609859/50000000000000 : ℝ), (43983733854403/100000000000000 : ℝ), (6543338452961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288858971/10000000000 : ℝ)|^8301 ≤ (21464794609859/50000000000000 : ℝ)^6253
        have hw : |(5288858971/10000000000 : ℝ)|=(5288858971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538639369/1000000000 : ℝ)|^8301 ≤ (43983733854403/100000000000000 : ℝ)^6253
        have hw : |(538639369/1000000000 : ℝ)|=(538639369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2161338643/10000000000 : ℝ)|^8301 ≤ (6543338452961/50000000000000 : ℝ)^6253
        have hw : |(-2161338643/10000000000 : ℝ)|=(2161338643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_11 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (224936703/500000000 : ℝ)*x 0 + (4306855511/10000000000 : ℝ)*x 1 + (4306855771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224936703/500000000 : ℝ)^8301 ≤ (34631355872503/100000000000000 : ℝ)^6253 := by
    have hnat : (224936703 : ℕ)^8301*100000000000000^6253 ≤ 34631355872503^6253*500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224936703 500000000 34631355872503 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4306855511/10000000000 : ℝ)^8301 ≤ (6536864149639/20000000000000 : ℝ)^6253 := by
    have hnat : (4306855511 : ℕ)^8301*20000000000000^6253 ≤ 6536864149639^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306855511 10000000000 6536864149639 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4306855771/10000000000 : ℝ)^8301 ≤ (653686467351/2000000000000 : ℝ)^6253 := by
    have hnat : (4306855771 : ℕ)^8301*2000000000000^6253 ≤ 653686467351^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306855771 10000000000 653686467351 2000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(224936703/500000000 : ℝ), (4306855511/10000000000 : ℝ), (4306855771/10000000000 : ℝ)] ![(34631355872503/100000000000000 : ℝ), (6536864149639/20000000000000 : ℝ), (653686467351/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(224936703/500000000 : ℝ)|^8301 ≤ (34631355872503/100000000000000 : ℝ)^6253
        have hw : |(224936703/500000000 : ℝ)|=(224936703/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4306855511/10000000000 : ℝ)|^8301 ≤ (6536864149639/20000000000000 : ℝ)^6253
        have hw : |(4306855511/10000000000 : ℝ)|=(4306855511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4306855771/10000000000 : ℝ)|^8301 ≤ (653686467351/2000000000000 : ℝ)^6253
        have hw : |(4306855771/10000000000 : ℝ)|=(4306855771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_12 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-527341369/2500000000 : ℝ)*x 0 + (5440774483/10000000000 : ℝ)*x 1 + (1054533887/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527341369/2500000000 : ℝ)^8301 ≤ (12670570135571/100000000000000 : ℝ)^6253 := by
    have hnat : (527341369 : ℕ)^8301*100000000000000^6253 ≤ 12670570135571^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527341369 2500000000 12670570135571 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440774483/10000000000 : ℝ)^8301 ≤ (4457420318661/10000000000000 : ℝ)^6253 := by
    have hnat : (5440774483 : ℕ)^8301*10000000000000^6253 ≤ 4457420318661^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440774483 10000000000 4457420318661 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054533887/2000000000 : ℝ)^8301 ≤ (42755226664769/100000000000000 : ℝ)^6253 := by
    have hnat : (1054533887 : ℕ)^8301*100000000000000^6253 ≤ 42755226664769^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054533887 2000000000 42755226664769 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527341369/2500000000 : ℝ), (5440774483/10000000000 : ℝ), (1054533887/2000000000 : ℝ)] ![(12670570135571/100000000000000 : ℝ), (4457420318661/10000000000000 : ℝ), (42755226664769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527341369/2500000000 : ℝ)|^8301 ≤ (12670570135571/100000000000000 : ℝ)^6253
        have hw : |(-527341369/2500000000 : ℝ)|=(527341369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440774483/10000000000 : ℝ)|^8301 ≤ (4457420318661/10000000000000 : ℝ)^6253
        have hw : |(5440774483/10000000000 : ℝ)|=(5440774483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054533887/2000000000 : ℝ)|^8301 ≤ (42755226664769/100000000000000 : ℝ)^6253
        have hw : |(1054533887/2000000000 : ℝ)|=(1054533887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_13 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369267849/10000000000 : ℝ)*x 0 + (-2205964727/10000000000 : ℝ)*x 1 + (527266949/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369267849/10000000000 : ℝ)^8301 ≤ (8759636720457/20000000000000 : ℝ)^6253 := by
    have hnat : (5369267849 : ℕ)^8301*20000000000000^6253 ≤ 8759636720457^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369267849 10000000000 8759636720457 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205964727/10000000000 : ℝ)^8301 ≤ (840411820341/6250000000000 : ℝ)^6253 := by
    have hnat : (2205964727 : ℕ)^8301*6250000000000^6253 ≤ 840411820341^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205964727 10000000000 840411820341 6250000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527266949/1000000000 : ℝ)^8301 ≤ (1710209090273/4000000000000 : ℝ)^6253 := by
    have hnat : (527266949 : ℕ)^8301*4000000000000^6253 ≤ 1710209090273^6253*1000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527266949 1000000000 1710209090273 4000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369267849/10000000000 : ℝ), (-2205964727/10000000000 : ℝ), (527266949/1000000000 : ℝ)] ![(8759636720457/20000000000000 : ℝ), (840411820341/6250000000000 : ℝ), (1710209090273/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369267849/10000000000 : ℝ)|^8301 ≤ (8759636720457/20000000000000 : ℝ)^6253
        have hw : |(5369267849/10000000000 : ℝ)|=(5369267849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2205964727/10000000000 : ℝ)|^8301 ≤ (840411820341/6250000000000 : ℝ)^6253
        have hw : |(-2205964727/10000000000 : ℝ)|=(2205964727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527266949/1000000000 : ℝ)|^8301 ≤ (1710209090273/4000000000000 : ℝ)^6253
        have hw : |(527266949/1000000000 : ℝ)|=(527266949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_14 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369269371/10000000000 : ℝ)*x 0 + (5272668211/10000000000 : ℝ)*x 1 + (-2205964391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369269371/10000000000 : ℝ)^8301 ≤ (21899100041911/50000000000000 : ℝ)^6253 := by
    have hnat : (5369269371 : ℕ)^8301*50000000000000^6253 ≤ 21899100041911^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369269371 10000000000 21899100041911 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272668211/10000000000 : ℝ)^8301 ≤ (8551042697763/20000000000000 : ℝ)^6253 := by
    have hnat : (5272668211 : ℕ)^8301*20000000000000^6253 ≤ 8551042697763^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272668211 10000000000 8551042697763 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205964391/10000000000 : ℝ)^8301 ≤ (6723293203273/50000000000000 : ℝ)^6253 := by
    have hnat : (2205964391 : ℕ)^8301*50000000000000^6253 ≤ 6723293203273^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205964391 10000000000 6723293203273 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369269371/10000000000 : ℝ), (5272668211/10000000000 : ℝ), (-2205964391/10000000000 : ℝ)] ![(21899100041911/50000000000000 : ℝ), (8551042697763/20000000000000 : ℝ), (6723293203273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369269371/10000000000 : ℝ)|^8301 ≤ (21899100041911/50000000000000 : ℝ)^6253
        have hw : |(5369269371/10000000000 : ℝ)|=(5369269371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272668211/10000000000 : ℝ)|^8301 ≤ (8551042697763/20000000000000 : ℝ)^6253
        have hw : |(5272668211/10000000000 : ℝ)|=(5272668211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2205964391/10000000000 : ℝ)|^8301 ≤ (6723293203273/50000000000000 : ℝ)^6253
        have hw : |(-2205964391/10000000000 : ℝ)|=(2205964391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_box_15 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66296133/156250000 : ℝ)*x 0 + (138585773/312500000 : ℝ)*x 1 + (2217371449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66296133/156250000 : ℝ)^8301 ≤ (16021051495617/50000000000000 : ℝ)^6253 := by
    have hnat : (66296133 : ℕ)^8301*50000000000000^6253 ≤ 16021051495617^6253*156250000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66296133 156250000 16021051495617 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138585773/312500000 : ℝ)^8301 ≤ (33978957844659/100000000000000 : ℝ)^6253 := by
    have hnat : (138585773 : ℕ)^8301*100000000000000^6253 ≤ 33978957844659^6253*312500000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138585773 312500000 33978957844659 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2217371449/5000000000 : ℝ)^8301 ≤ (33978939149511/100000000000000 : ℝ)^6253 := by
    have hnat : (2217371449 : ℕ)^8301*100000000000000^6253 ≤ 33978939149511^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217371449 5000000000 33978939149511 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66296133/156250000 : ℝ), (138585773/312500000 : ℝ), (2217371449/5000000000 : ℝ)] ![(16021051495617/50000000000000 : ℝ), (33978957844659/100000000000000 : ℝ), (33978939149511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66296133/156250000 : ℝ)|^8301 ≤ (16021051495617/50000000000000 : ℝ)^6253
        have hw : |(66296133/156250000 : ℝ)|=(66296133/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(138585773/312500000 : ℝ)|^8301 ≤ (33978957844659/100000000000000 : ℝ)^6253
        have hw : |(138585773/312500000 : ℝ)|=(138585773/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2217371449/5000000000 : ℝ)|^8301 ≤ (33978939149511/100000000000000 : ℝ)^6253
        have hw : |(2217371449/5000000000 : ℝ)|=(2217371449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1108_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15557/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7409/12500 : ℝ) ∧ (79703/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10381/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3507/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3507/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3507/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3507/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3507/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3507/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11309/100000 : ℝ) ^ (2075/512 : ℝ) ≤ (1822593202880701/12500000000000000000 : ℝ) := by
    have hpowers : (11309/100000 : ℝ)^2075 ≤ (1822593202880701/12500000000000000000 : ℝ)^512 := by
      have hnat : (11309 : ℕ)^2075*12500000000000000000^512 ≤ 1822593202880701^512*100000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11309 100000 1822593202880701 12500000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11309/100000 : ℝ)) (X := (1822593202880701/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3507/25000 : ℝ) ^ (2075/512 : ℝ) ≤ (6982812471210797/20000000000000000000 : ℝ) := by
    have hpowers : (3507/25000 : ℝ)^2075 ≤ (6982812471210797/20000000000000000000 : ℝ)^512 := by
      have hnat : (3507 : ℕ)^2075*20000000000000000000^512 ≤ 6982812471210797^512*25000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3507 25000 6982812471210797 20000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3507/25000 : ℝ)) (X := (6982812471210797/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251822593202880701/6250000000000000000 : ℝ) ≤ (5000359735999081/5000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (6251822593202880701/6250000000000000000 : ℝ)^512 ≤ (5000359735999081/5000000000000000 : ℝ)^2075 := by
      have hnat : (6251822593202880701 : ℕ)^512*5000000000000000^2075 ≤ 5000359735999081^2075*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251822593202880701 6250000000000000000 5000359735999081 5000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000359735999081/5000000000000000 : ℝ)) (X := (6251822593202880701/6250000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049494807979099593/100000000000000000000 : ℝ) ≤ (78134539389743/78125000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (100049494807979099593/100000000000000000000 : ℝ)^512 ≤ (78134539389743/78125000000000 : ℝ)^2075 := by
      have hnat : (100049494807979099593 : ℕ)^512*78125000000000^2075 ≤ 78134539389743^2075*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049494807979099593 100000000000000000000 78134539389743 78125000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78134539389743/78125000000000 : ℝ)) (X := (100049494807979099593/100000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006982812471210797/10000000000000000000 : ℝ) ≤ (5000861305888023/5000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (10006982812471210797/10000000000000000000 : ℝ)^512 ≤ (5000861305888023/5000000000000000 : ℝ)^2075 := by
      have hnat : (10006982812471210797 : ℕ)^512*5000000000000000^2075 ≤ 5000861305888023^2075*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006982812471210797 10000000000000000000 5000861305888023 5000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000861305888023/5000000000000000 : ℝ)) (X := (10006982812471210797/10000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1822593202880701/12500000000000000000 : ℝ) ≤ ((13590305868307456161/13595000000000000000 : ℝ)+2*(250784944471/135950000000000 : ℝ)*(11309/100000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (13590305868307456161/13595000000000000000 : ℝ)+2*(250784944471/135950000000000 : ℝ)*(11309/100000 : ℝ)=(5000359735999081/5000000000000000 : ℝ) by norm_num, show 1+2*(1822593202880701/12500000000000000000 : ℝ)=(6251822593202880701/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6982812471210797/20000000000000000000 : ℝ)+(1822593202880701/12500000000000000000 : ℝ) ≤ ((13590305868307456161/13595000000000000000 : ℝ)+(250784944471/135950000000000 : ℝ)*((3507/25000 : ℝ)+(11309/100000 : ℝ)))^(2075/512 : ℝ) := by
    rw [show (13590305868307456161/13595000000000000000 : ℝ)+(250784944471/135950000000000 : ℝ)*((3507/25000 : ℝ)+(11309/100000 : ℝ))=(78134539389743/78125000000000 : ℝ) by norm_num, show 1+(6982812471210797/20000000000000000000 : ℝ)+(1822593202880701/12500000000000000000 : ℝ)=(100049494807979099593/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6982812471210797/20000000000000000000 : ℝ) ≤ ((13590305868307456161/13595000000000000000 : ℝ)+2*(250784944471/135950000000000 : ℝ)*(3507/25000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (13590305868307456161/13595000000000000000 : ℝ)+2*(250784944471/135950000000000 : ℝ)*(3507/25000 : ℝ)=(5000861305888023/5000000000000000 : ℝ) by norm_num, show 1+2*(6982812471210797/20000000000000000000 : ℝ)=(10006982812471210797/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13590305868307456161/13595000000000000000 : ℝ)*(X 1 0+X 2 0)+(250784944471/135950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (13590305868307456161/13595000000000000000 : ℝ)) (alpha := (250784944471/135950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13590305868307456161/13595000000000000000 : ℝ)*(X 0 1+X 2 1)+(250784944471/135950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (13590305868307456161/13595000000000000000 : ℝ)) (alpha := (250784944471/135950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13590305868307456161/13595000000000000000 : ℝ)*(X 0 2+X 1 2)+(250784944471/135950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (13590305868307456161/13595000000000000000 : ℝ)) (alpha := (250784944471/135950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1027615757/5000000000 : ℝ)*X 0 0+(5376788281/10000000000 : ℝ)*X 0 1+(1344197053/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1323913449/2500000000 : ℝ)*X 1 0+(-135323551/625000000 : ℝ)*X 1 1+(2688394171/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295653873/10000000000 : ℝ)*X 2 0+(2688394053/5000000000 : ℝ)*X 2 1+(-2165177031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((895479881/2000000000 : ℝ)*X 0 0+(4317663217/10000000000 : ℝ)*X 0 1+(134926993/312500000 : ℝ)*X 0 2+(895479881/2000000000 : ℝ)*X 1 0+(4317663217/10000000000 : ℝ)*X 1 1+(134926993/312500000 : ℝ)*X 1 2+(895479881/2000000000 : ℝ)*X 2 0+(4317663217/10000000000 : ℝ)*X 2 1+(134926993/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-578166793/2500000000 : ℝ)*X 0 0+(1056138341/2000000000 : ℝ)*X 0 1+(528069153/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363598247/10000000000 : ℝ)*X 1 0+(-2202875511/10000000000 : ℝ)*X 1 1+(2640345803/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681799129/5000000000 : ℝ)*X 2 0+(2640345753/5000000000 : ℝ)*X 2 1+(-2202875631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((852245789/2000000000 : ℝ)*X 0 0+(553215981/1250000000 : ℝ)*X 0 1+(4425727387/10000000000 : ℝ)*X 0 2+(852245789/2000000000 : ℝ)*X 1 0+(553215981/1250000000 : ℝ)*X 1 1+(4425727387/10000000000 : ℝ)*X 1 2+(852245789/2000000000 : ℝ)*X 2 0+(553215981/1250000000 : ℝ)*X 2 1+(4425727387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1129436797/5000000000 : ℝ)*X 0 0+(1303850619/2500000000 : ℝ)*X 0 1+(5386393701/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644429429/5000000000 : ℝ)*X 1 0+(-2161338961/10000000000 : ℝ)*X 1 1+(5386393567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288858971/10000000000 : ℝ)*X 2 0+(538639369/1000000000 : ℝ)*X 2 1+(-2161338643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((224936703/500000000 : ℝ)*X 0 0+(4306855511/10000000000 : ℝ)*X 0 1+(4306855771/10000000000 : ℝ)*X 0 2+(224936703/500000000 : ℝ)*X 1 0+(4306855511/10000000000 : ℝ)*X 1 1+(4306855771/10000000000 : ℝ)*X 1 2+(224936703/500000000 : ℝ)*X 2 0+(4306855511/10000000000 : ℝ)*X 2 1+(4306855771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-527341369/2500000000 : ℝ)*X 0 0+(5440774483/10000000000 : ℝ)*X 0 1+(1054533887/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369267849/10000000000 : ℝ)*X 1 0+(-2205964727/10000000000 : ℝ)*X 1 1+(527266949/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369269371/10000000000 : ℝ)*X 2 0+(5272668211/10000000000 : ℝ)*X 2 1+(-2205964391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((66296133/156250000 : ℝ)*X 0 0+(138585773/312500000 : ℝ)*X 0 1+(2217371449/5000000000 : ℝ)*X 0 2+(66296133/156250000 : ℝ)*X 1 0+(138585773/312500000 : ℝ)*X 1 1+(2217371449/5000000000 : ℝ)*X 1 2+(66296133/156250000 : ℝ)*X 2 0+(138585773/312500000 : ℝ)*X 2 1+(2217371449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15557/25000 : ℝ) ≤ (-211487381755146683242946156968533/339875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5665413/100000000000000 : ℝ)*(lower0) + (14131381/25000000000000 : ℝ)*(upper1) + (1173029/2500000000000 : ℝ)*(upper3) + (70568811/100000000000000 : ℝ)*(lower5) + (1946046165817649/50000000000000 : ℝ)*(major0) + (1946046165817649/50000000000000 : ℝ)*(major1) + (1946046165817649/50000000000000 : ℝ)*(major2) + (33606357/4000000000000 : ℝ)*(sp2) + (103789148079407/2000000000000 : ℝ)*(sp4) + (1297365510956517/25000000000000 : ℝ)*(sp5) + (5189461203667143/100000000000000 : ℝ)*(sp6) + (1307725814007971/50000000000000 : ℝ)*(sp7) + (2319927859/50000000000000 : ℝ)*(sp8) + (12674082009/100000000000000 : ℝ)*(sp15) + (52309286041959/2000000000000 : ℝ)*(f.failure) + (1297365510956517/25000000000000 : ℝ)*(f.sum) + (16283603940677/6797500000000000000000000000 : ℝ)*base66 + (21859537269204985489/679750000000000000000000000000000 : ℝ)*base67 + (14492868377701014511/679750000000000000000000000000000 : ℝ)*base70 + (2475029181116014511/679750000000000000000000000000000 : ℝ)*base72 + (2473761437689/849687500000000000000000000 : ℝ)*base74 + (31178570651446485489/679750000000000000000000000000000 : ℝ)*base75 + (3168850429600264511/679750000000000000000000000000000 : ℝ)*base78 + (13440035818772514511/679750000000000000000000000000000 : ℝ)*base80 + (144704592120639/3398750000000000000000000000 : ℝ)*base81 + (720799/200000000000000000000 : ℝ)*base89 + (720799/200000000000000000000 : ℝ)*base91 + (720799/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (7409/12500 : ℝ) ≤ (201460654278312108141071890118613/339875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48420257/50000000000000 : ℝ)*(upper0) + (91449237/100000000000000 : ℝ)*(upper2) + (1585739/12500000000000 : ℝ)*(upper5) + (1977844234350889/50000000000000 : ℝ)*(major0) + (1977844234350889/50000000000000 : ℝ)*(major1) + (1977844234350889/50000000000000 : ℝ)*(major2) + (2616705742022857/50000000000000 : ℝ)*(sp0) + (5233403853813927/100000000000000 : ℝ)*(sp1) + (5233366418699163/100000000000000 : ℝ)*(sp2) + (265819884685401/10000000000000 : ℝ)*(sp3) + (14224067609/100000000000000 : ℝ)*(sp5) + (1704046861/100000000000000 : ℝ)*(sp7) + (51659182373/100000000000000 : ℝ)*(sp10) + (3296917911/50000000000000 : ℝ)*(sp12) + (2658200550900871/100000000000000 : ℝ)*(f.failure) + (81772157466899/1562500000000 : ℝ)*(f.sum) + (51706486951189/13595000000000000000000000000 : ℝ)*base66 + (21952035741569722871/679750000000000000000000000000000 : ℝ)*base68 + (3623418695707027129/679750000000000000000000000000000 : ℝ)*base69 + (6472450720833277129/679750000000000000000000000000000 : ℝ)*base71 + (56067113653989/13595000000000000000000000000 : ℝ)*base74 + (2412236644994527129/679750000000000000000000000000000 : ℝ)*base75 + (4194069475684972871/679750000000000000000000000000000 : ℝ)*base78 + (4446345090087277129/679750000000000000000000000000000 : ℝ)*base79 + (8608877314251/13595000000000000000000000000 : ℝ)*base81 + (49072831/10000000000000000000000 : ℝ)*base89 + (49072831/10000000000000000000000 : ℝ)*base91 + (49072831/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79703/100000 : ℝ) ≤ (270900687162387095464546204753317/339875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65602407/100000000000000 : ℝ)*(upper0) + (30974951/100000000000000 : ℝ)*(lower1) + (58140231/50000000000000 : ℝ)*(lower3) + (155326107/100000000000000 : ℝ)*(upper4) + (2211898189329599/50000000000000 : ℝ)*(major0) + (2211898189329599/50000000000000 : ℝ)*(major1) + (2211898189329599/50000000000000 : ℝ)*(major2) + (7224045667/100000000000000 : ℝ)*(sp1) + (13855901053/10000000000000 : ℝ)*(sp2) + (26248755979/25000000000000 : ℝ)*(sp3) + (5848257647414329/100000000000000 : ℝ)*(sp8) + (5848250423368661/100000000000000 : ℝ)*(sp9) + (5848119088403799/100000000000000 : ℝ)*(sp10) + (743165364023153/25000000000000 : ℝ)*(sp11) + (185797903194783/6250000000000 : ℝ)*(f.failure) + (5848257647414329/100000000000000 : ℝ)*(f.sum) + (16679697246743/6797500000000000000000000000 : ℝ)*base65 + (928009481777890561/679750000000000000000000000000000 : ℝ)*base68 + (6111314762500640561/679750000000000000000000000000000 : ℝ)*base70 + (3577220804227609439/679750000000000000000000000000000 : ℝ)*base71 + (40666994736029/13595000000000000000000000000 : ℝ)*base74 + (3268788058392640561/679750000000000000000000000000000 : ℝ)*base76 + (315397979519859439/679750000000000000000000000000000 : ℝ)*base77 + (11446397007786390561/679750000000000000000000000000000 : ℝ)*base80 + (227248294321/13595000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1959863/625000000000000000000 : ℝ)*base89 + (1959863/625000000000000000000 : ℝ)*base91 + (1959863/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-10381/12500 : ℝ) ≤ (-7056265348785772586087170589967/8496875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224502497/100000000000000 : ℝ)*(lower0) + (4472921/50000000000000 : ℝ)*(lower1) + (328488801/50000000000000 : ℝ)*(lower2) + (111463564179649/2500000000000 : ℝ)*(major0) + (111463564179649/2500000000000 : ℝ)*(major1) + (111463564179649/2500000000000 : ℝ)*(major2) + (27083301451/100000000000000 : ℝ)*(sp0) + (160940257477/50000000000000 : ℝ)*(sp5) + (189954140867/25000000000000 : ℝ)*(sp6) + (5329631053/50000000000000 : ℝ)*(sp7) + (2974312080670501/50000000000000 : ℝ)*(sp12) + (5948329364127499/100000000000000 : ℝ)*(sp13) + (1189578285615797/20000000000000 : ℝ)*(sp14) + (1498052518210327/50000000000000 : ℝ)*(sp15) + (74902892392069/2500000000000 : ℝ)*(f.failure) + (5948651244642453/100000000000000 : ℝ)*(f.sum) + (6194286268169/679750000000000000000000000 : ℝ)*base65 + (411048457139379989/33987500000000000000000000000000 : ℝ)*base67 + (363335823522217489/33987500000000000000000000000000 : ℝ)*base69 + (112112985454604989/33987500000000000000000000000000 : ℝ)*base71 + (78640614607971/2719000000000000000000000000 : ℝ)*base74 + (249286955506117489/33987500000000000000000000000000 : ℝ)*base75 + (282344752968229989/33987500000000000000000000000000 : ℝ)*base77 + (1604879352512795011/33987500000000000000000000000000 : ℝ)*base80 + (1112191240523/543800000000000000000000000 : ℝ)*base81 + (1745491/250000000000000000000 : ℝ)*base90 + (1745491/250000000000000000000 : ℝ)*base92 + (1745491/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1108_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(7409/12500 : ℝ) else (79703/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10381/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1108_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1108_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(7409/12500 : ℝ) else (79703/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10381/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1108_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1108_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(7409/12500 : ℝ) else (79703/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10381/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1108_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
