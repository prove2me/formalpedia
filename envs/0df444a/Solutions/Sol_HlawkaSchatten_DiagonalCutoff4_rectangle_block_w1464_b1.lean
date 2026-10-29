-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1464_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:08:41.67719+00:00
-- url     : https://prove2.me/submissions/8e514b78-11fa-4000-ae40-4c60d0ff43df

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
theorem support_rectangle_w1464_s3_0 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-970226467/5000000000 : ℝ)*x 0 + (5445189217/10000000000 : ℝ)*x 1 + (5209758837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (970226467/5000000000 : ℝ)^4425 ≤ (11844025839753/100000000000000 : ℝ)^3401 := by
    have hnat : (970226467 : ℕ)^4425*100000000000000^3401 ≤ 11844025839753^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970226467 5000000000 11844025839753 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445189217/10000000000 : ℝ)^4425 ≤ (1813801114303/4000000000000 : ℝ)^3401 := by
    have hnat : (5445189217 : ℕ)^4425*4000000000000^3401 ≤ 1813801114303^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445189217 10000000000 1813801114303 4000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5209758837/10000000000 : ℝ)^4425 ≤ (4281094628987/10000000000000 : ℝ)^3401 := by
    have hnat : (5209758837 : ℕ)^4425*10000000000000^3401 ≤ 4281094628987^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5209758837 10000000000 4281094628987 10000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-970226467/5000000000 : ℝ), (5445189217/10000000000 : ℝ), (5209758837/10000000000 : ℝ)] ![(11844025839753/100000000000000 : ℝ), (1813801114303/4000000000000 : ℝ), (4281094628987/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-970226467/5000000000 : ℝ)|^4425 ≤ (11844025839753/100000000000000 : ℝ)^3401
        have hw : |(-970226467/5000000000 : ℝ)|=(970226467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445189217/10000000000 : ℝ)|^4425 ≤ (1813801114303/4000000000000 : ℝ)^3401
        have hw : |(5445189217/10000000000 : ℝ)|=(5445189217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5209758837/10000000000 : ℝ)|^4425 ≤ (4281094628987/10000000000000 : ℝ)^3401
        have hw : |(5209758837/10000000000 : ℝ)|=(5209758837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s3_1 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535557589/1000000000 : ℝ)*x 0 + (-1030647197/5000000000 : ℝ)*x 1 + (40701241/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535557589/1000000000 : ℝ)^4425 ≤ (5547061848439/12500000000000 : ℝ)^3401 := by
    have hnat : (535557589 : ℕ)^4425*12500000000000^3401 ≤ 5547061848439^3401*1000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535557589 1000000000 5547061848439 12500000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030647197/5000000000 : ℝ)^4425 ≤ (6406279395681/50000000000000 : ℝ)^3401 := by
    have hnat : (1030647197 : ℕ)^4425*50000000000000^3401 ≤ 6406279395681^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030647197 5000000000 6406279395681 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40701241/78125000 : ℝ)^4425 ≤ (21405473203739/50000000000000 : ℝ)^3401 := by
    have hnat : (40701241 : ℕ)^4425*50000000000000^3401 ≤ 21405473203739^3401*78125000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40701241 78125000 21405473203739 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535557589/1000000000 : ℝ), (-1030647197/5000000000 : ℝ), (40701241/78125000 : ℝ)] ![(5547061848439/12500000000000 : ℝ), (6406279395681/50000000000000 : ℝ), (21405473203739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535557589/1000000000 : ℝ)|^4425 ≤ (5547061848439/12500000000000 : ℝ)^3401
        have hw : |(535557589/1000000000 : ℝ)|=(535557589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030647197/5000000000 : ℝ)|^4425 ≤ (6406279395681/50000000000000 : ℝ)^3401
        have hw : |(-1030647197/5000000000 : ℝ)|=(1030647197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40701241/78125000 : ℝ)|^4425 ≤ (21405473203739/50000000000000 : ℝ)^3401
        have hw : |(40701241/78125000 : ℝ)|=(40701241/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s3_2 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071115181/2000000000 : ℝ)*x 0 + (5209758839/10000000000 : ℝ)*x 1 + (-1030647193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071115181/2000000000 : ℝ)^4425 ≤ (1775059797969/4000000000000 : ℝ)^3401 := by
    have hnat : (1071115181 : ℕ)^4425*4000000000000^3401 ≤ 1775059797969^3401*2000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071115181 2000000000 1775059797969 4000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5209758839/10000000000 : ℝ)^4425 ≤ (21405473155627/50000000000000 : ℝ)^3401 := by
    have hnat : (5209758839 : ℕ)^4425*50000000000000^3401 ≤ 21405473155627^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5209758839 10000000000 21405473155627 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030647193/5000000000 : ℝ)^4425 ≤ (12812558726663/100000000000000 : ℝ)^3401 := by
    have hnat : (1030647193 : ℕ)^4425*100000000000000^3401 ≤ 12812558726663^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030647193 5000000000 12812558726663 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071115181/2000000000 : ℝ), (5209758839/10000000000 : ℝ), (-1030647193/5000000000 : ℝ)] ![(1775059797969/4000000000000 : ℝ), (21405473155627/50000000000000 : ℝ), (12812558726663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071115181/2000000000 : ℝ)|^4425 ≤ (1775059797969/4000000000000 : ℝ)^3401
        have hw : |(1071115181/2000000000 : ℝ)|=(1071115181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5209758839/10000000000 : ℝ)|^4425 ≤ (21405473155627/50000000000000 : ℝ)^3401
        have hw : |(5209758839/10000000000 : ℝ)|=(5209758839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030647193/5000000000 : ℝ)|^4425 ≤ (12812558726663/100000000000000 : ℝ)^3401
        have hw : |(-1030647193/5000000000 : ℝ)|=(1030647193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s3_3 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536514741/1250000000 : ℝ)*x 0 + (2020520811/5000000000 : ℝ)*x 1 + (2278447059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536514741/1250000000 : ℝ)^4425 ≤ (6654317415937/20000000000000 : ℝ)^3401 := by
    have hnat : (536514741 : ℕ)^4425*20000000000000^3401 ≤ 6654317415937^3401*1250000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536514741 1250000000 6654317415937 20000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2020520811/5000000000 : ℝ)^4425 ≤ (480654756929/1562500000000 : ℝ)^3401 := by
    have hnat : (2020520811 : ℕ)^4425*1562500000000^3401 ≤ 480654756929^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020520811 5000000000 480654756929 1562500000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2278447059/5000000000 : ℝ)^4425 ≤ (7193301691857/20000000000000 : ℝ)^3401 := by
    have hnat : (2278447059 : ℕ)^4425*20000000000000^3401 ≤ 7193301691857^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278447059 5000000000 7193301691857 20000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536514741/1250000000 : ℝ), (2020520811/5000000000 : ℝ), (2278447059/5000000000 : ℝ)] ![(6654317415937/20000000000000 : ℝ), (480654756929/1562500000000 : ℝ), (7193301691857/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536514741/1250000000 : ℝ)|^4425 ≤ (6654317415937/20000000000000 : ℝ)^3401
        have hw : |(536514741/1250000000 : ℝ)|=(536514741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2020520811/5000000000 : ℝ)|^4425 ≤ (480654756929/1562500000000 : ℝ)^3401
        have hw : |(2020520811/5000000000 : ℝ)|=(2020520811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2278447059/5000000000 : ℝ)|^4425 ≤ (7193301691857/20000000000000 : ℝ)^3401
        have hw : |(2278447059/5000000000 : ℝ)|=(2278447059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s3_4 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-121280531/625000000 : ℝ)*x 0 + (5211016517/10000000000 : ℝ)*x 1 + (680490251/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121280531/625000000 : ℝ)^4425 ≤ (5922154128187/50000000000000 : ℝ)^3401 := by
    have hnat : (121280531 : ℕ)^4425*50000000000000^3401 ≤ 5922154128187^3401*625000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121280531 625000000 5922154128187 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5211016517/10000000000 : ℝ)^4425 ≤ (42824393425571/100000000000000 : ℝ)^3401 := by
    have hnat : (5211016517 : ℕ)^4425*100000000000000^3401 ≤ 42824393425571^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5211016517 10000000000 42824393425571 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680490251/1250000000 : ℝ)^4425 ≤ (45331298305377/100000000000000 : ℝ)^3401 := by
    have hnat : (680490251 : ℕ)^4425*100000000000000^3401 ≤ 45331298305377^3401*1250000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680490251 1250000000 45331298305377 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121280531/625000000 : ℝ), (5211016517/10000000000 : ℝ), (680490251/1250000000 : ℝ)] ![(5922154128187/50000000000000 : ℝ), (42824393425571/100000000000000 : ℝ), (45331298305377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121280531/625000000 : ℝ)|^4425 ≤ (5922154128187/50000000000000 : ℝ)^3401
        have hw : |(-121280531/625000000 : ℝ)|=(121280531/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5211016517/10000000000 : ℝ)|^4425 ≤ (42824393425571/100000000000000 : ℝ)^3401
        have hw : |(5211016517/10000000000 : ℝ)|=(5211016517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(680490251/1250000000 : ℝ)|^4425 ≤ (45331298305377/100000000000000 : ℝ)^3401
        have hw : |(680490251/1250000000 : ℝ)|=(680490251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s3_5 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661782457/1250000000 : ℝ)*x 0 + (-1827131379/10000000000 : ℝ)*x 1 + (2721961089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661782457/1250000000 : ℝ)^4425 ≤ (5464574423249/12500000000000 : ℝ)^3401 := by
    have hnat : (661782457 : ℕ)^4425*12500000000000^3401 ≤ 5464574423249^3401*1250000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661782457 1250000000 5464574423249 12500000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1827131379/10000000000 : ℝ)^4425 ≤ (547605222627/5000000000000 : ℝ)^3401 := by
    have hnat : (1827131379 : ℕ)^4425*5000000000000^3401 ≤ 547605222627^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827131379 10000000000 547605222627 5000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721961089/5000000000 : ℝ)^4425 ≤ (22665650073587/50000000000000 : ℝ)^3401 := by
    have hnat : (2721961089 : ℕ)^4425*50000000000000^3401 ≤ 22665650073587^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721961089 5000000000 22665650073587 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661782457/1250000000 : ℝ), (-1827131379/10000000000 : ℝ), (2721961089/5000000000 : ℝ)] ![(5464574423249/12500000000000 : ℝ), (547605222627/5000000000000 : ℝ), (22665650073587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661782457/1250000000 : ℝ)|^4425 ≤ (5464574423249/12500000000000 : ℝ)^3401
        have hw : |(661782457/1250000000 : ℝ)|=(661782457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1827131379/10000000000 : ℝ)|^4425 ≤ (547605222627/5000000000000 : ℝ)^3401
        have hw : |(-1827131379/10000000000 : ℝ)|=(1827131379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721961089/5000000000 : ℝ)|^4425 ≤ (22665650073587/50000000000000 : ℝ)^3401
        have hw : |(2721961089/5000000000 : ℝ)|=(2721961089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s3_6 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132356499/250000000 : ℝ)*x 0 + (217756883/400000000 : ℝ)*x 1 + (-57097847/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132356499/250000000 : ℝ)^4425 ≤ (43716598652031/100000000000000 : ℝ)^3401 := by
    have hnat : (132356499 : ℕ)^4425*100000000000000^3401 ≤ 43716598652031^3401*250000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132356499 250000000 43716598652031 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217756883/400000000 : ℝ)^4425 ≤ (22665649515631/50000000000000 : ℝ)^3401 := by
    have hnat : (217756883 : ℕ)^4425*50000000000000^3401 ≤ 22665649515631^3401*400000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217756883 400000000 22665649515631 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57097847/312500000 : ℝ)^4425 ≤ (10952102307837/100000000000000 : ℝ)^3401 := by
    have hnat : (57097847 : ℕ)^4425*100000000000000^3401 ≤ 10952102307837^3401*312500000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57097847 312500000 10952102307837 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132356499/250000000 : ℝ), (217756883/400000000 : ℝ), (-57097847/312500000 : ℝ)] ![(43716598652031/100000000000000 : ℝ), (22665649515631/50000000000000 : ℝ), (10952102307837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132356499/250000000 : ℝ)|^4425 ≤ (43716598652031/100000000000000 : ℝ)^3401
        have hw : |(132356499/250000000 : ℝ)|=(132356499/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217756883/400000000 : ℝ)|^4425 ≤ (22665649515631/50000000000000 : ℝ)^3401
        have hw : |(217756883/400000000 : ℝ)|=(217756883/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-57097847/312500000 : ℝ)|^4425 ≤ (10952102307837/100000000000000 : ℝ)^3401
        have hw : |(-57097847/312500000 : ℝ)|=(57097847/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s3_7 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4292196213/10000000000 : ℝ)*x 0 + (4554138943/10000000000 : ℝ)*x 1 + (126369313/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4292196213/10000000000 : ℝ)^4425 ≤ (16636188322683/50000000000000 : ℝ)^3401 := by
    have hnat : (4292196213 : ℕ)^4425*50000000000000^3401 ≤ 16636188322683^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4292196213 10000000000 16636188322683 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4554138943/10000000000 : ℝ)^4425 ≤ (35938217632693/100000000000000 : ℝ)^3401 := by
    have hnat : (4554138943 : ℕ)^4425*100000000000000^3401 ≤ 35938217632693^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554138943 10000000000 35938217632693 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126369313/312500000 : ℝ)^4425 ≤ (30789405700513/100000000000000 : ℝ)^3401 := by
    have hnat : (126369313 : ℕ)^4425*100000000000000^3401 ≤ 30789405700513^3401*312500000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126369313 312500000 30789405700513 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4292196213/10000000000 : ℝ), (4554138943/10000000000 : ℝ), (126369313/312500000 : ℝ)] ![(16636188322683/50000000000000 : ℝ), (35938217632693/100000000000000 : ℝ), (30789405700513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4292196213/10000000000 : ℝ)|^4425 ≤ (16636188322683/50000000000000 : ℝ)^3401
        have hw : |(4292196213/10000000000 : ℝ)|=(4292196213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4554138943/10000000000 : ℝ)|^4425 ≤ (35938217632693/100000000000000 : ℝ)^3401
        have hw : |(4554138943/10000000000 : ℝ)|=(4554138943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(126369313/312500000 : ℝ)|^4425 ≤ (30789405700513/100000000000000 : ℝ)^3401
        have hw : |(126369313/312500000 : ℝ)|=(126369313/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1464_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16209/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10039/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (663/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3897/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16209/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10039/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16209/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10039/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16209/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10039/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16209/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10039/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16209/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10039/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16209/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10039/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10039/100000 : ℝ) ^ (4423/1024 : ℝ) ≤ (4874899897597847/100000000000000000000 : ℝ) := by
    have hpowers : (10039/100000 : ℝ)^4423 ≤ (4874899897597847/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10039 : ℕ)^4423*100000000000000000000^1024 ≤ 4874899897597847^1024*100000^4423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10039 100000 4874899897597847 100000000000000000000 4423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10039/100000 : ℝ)) (X := (4874899897597847/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16209/100000 : ℝ) ^ (4423/1024 : ℝ) ≤ (38607497448578439/100000000000000000000 : ℝ) := by
    have hpowers : (16209/100000 : ℝ)^4423 ≤ (38607497448578439/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16209 : ℕ)^4423*100000000000000000000^1024 ≤ 38607497448578439^1024*100000^4423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16209 100000 38607497448578439 100000000000000000000 4423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16209/100000 : ℝ)) (X := (38607497448578439/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004874899897597847/50000000000000000000 : ℝ) ≤ (10000225716052253/10000000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (50004874899897597847/50000000000000000000 : ℝ)^1024 ≤ (10000225716052253/10000000000000000 : ℝ)^4423 := by
      have hnat : (50004874899897597847 : ℕ)^1024*10000000000000000^4423 ≤ 10000225716052253^4423*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004874899897597847 50000000000000000000 10000225716052253 10000000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000225716052253/10000000000000000 : ℝ)) (X := (50004874899897597847/50000000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021741198673088143/50000000000000000000 : ℝ) ≤ (10001006523570081/10000000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (50021741198673088143/50000000000000000000 : ℝ)^1024 ≤ (10001006523570081/10000000000000000 : ℝ)^4423 := by
      have hnat : (50021741198673088143 : ℕ)^1024*10000000000000000^4423 ≤ 10001006523570081^4423*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021741198673088143 50000000000000000000 10001006523570081 10000000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001006523570081/10000000000000000 : ℝ)) (X := (50021741198673088143/50000000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038607497448578439/50000000000000000000 : ℝ) ≤ (10001787331087909/10000000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (50038607497448578439/50000000000000000000 : ℝ)^1024 ≤ (10001787331087909/10000000000000000 : ℝ)^4423 := by
      have hnat : (50038607497448578439 : ℕ)^1024*10000000000000000^4423 ≤ 10001787331087909^4423*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038607497448578439 50000000000000000000 10001787331087909 10000000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001787331087909/10000000000000000 : ℝ)) (X := (50038607497448578439/50000000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4874899897597847/100000000000000000000 : ℝ) ≤ ((30842857807349725213/30850000000000000000 : ℝ)+2*(195201879457/154250000000000 : ℝ)*(10039/100000 : ℝ))^(4423/1024 : ℝ) := by
    rw [show (30842857807349725213/30850000000000000000 : ℝ)+2*(195201879457/154250000000000 : ℝ)*(10039/100000 : ℝ)=(10000225716052253/10000000000000000 : ℝ) by norm_num, show 1+2*(4874899897597847/100000000000000000000 : ℝ)=(50004874899897597847/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38607497448578439/100000000000000000000 : ℝ)+(4874899897597847/100000000000000000000 : ℝ) ≤ ((30842857807349725213/30850000000000000000 : ℝ)+(195201879457/154250000000000 : ℝ)*((16209/100000 : ℝ)+(10039/100000 : ℝ)))^(4423/1024 : ℝ) := by
    rw [show (30842857807349725213/30850000000000000000 : ℝ)+(195201879457/154250000000000 : ℝ)*((16209/100000 : ℝ)+(10039/100000 : ℝ))=(10001006523570081/10000000000000000 : ℝ) by norm_num, show 1+(38607497448578439/100000000000000000000 : ℝ)+(4874899897597847/100000000000000000000 : ℝ)=(50021741198673088143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38607497448578439/100000000000000000000 : ℝ) ≤ ((30842857807349725213/30850000000000000000 : ℝ)+2*(195201879457/154250000000000 : ℝ)*(16209/100000 : ℝ))^(4423/1024 : ℝ) := by
    rw [show (30842857807349725213/30850000000000000000 : ℝ)+2*(195201879457/154250000000000 : ℝ)*(16209/100000 : ℝ)=(10001787331087909/10000000000000000 : ℝ) by norm_num, show 1+2*(38607497448578439/100000000000000000000 : ℝ)=(50038607497448578439/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30842857807349725213/30850000000000000000 : ℝ)*(X 1 0+X 2 0)+(195201879457/154250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (10039/100000 : ℝ)) (hi := (16209/100000 : ℝ)) (c := (30842857807349725213/30850000000000000000 : ℝ)) (alpha := (195201879457/154250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30842857807349725213/30850000000000000000 : ℝ)*(X 0 1+X 2 1)+(195201879457/154250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (10039/100000 : ℝ)) (hi := (16209/100000 : ℝ)) (c := (30842857807349725213/30850000000000000000 : ℝ)) (alpha := (195201879457/154250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30842857807349725213/30850000000000000000 : ℝ)*(X 0 2+X 1 2)+(195201879457/154250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (10039/100000 : ℝ)) (hi := (16209/100000 : ℝ)) (c := (30842857807349725213/30850000000000000000 : ℝ)) (alpha := (195201879457/154250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-970226467/5000000000 : ℝ)*X 0 0+(5445189217/10000000000 : ℝ)*X 0 1+(5209758837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535557589/1000000000 : ℝ)*X 1 0+(-1030647197/5000000000 : ℝ)*X 1 1+(40701241/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071115181/2000000000 : ℝ)*X 2 0+(5209758839/10000000000 : ℝ)*X 2 1+(-1030647193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((536514741/1250000000 : ℝ)*X 0 0+(2020520811/5000000000 : ℝ)*X 0 1+(2278447059/5000000000 : ℝ)*X 0 2+(536514741/1250000000 : ℝ)*X 1 0+(2020520811/5000000000 : ℝ)*X 1 1+(2278447059/5000000000 : ℝ)*X 1 2+(536514741/1250000000 : ℝ)*X 2 0+(2020520811/5000000000 : ℝ)*X 2 1+(2278447059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-121280531/625000000 : ℝ)*X 0 0+(5211016517/10000000000 : ℝ)*X 0 1+(680490251/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661782457/1250000000 : ℝ)*X 1 0+(-1827131379/10000000000 : ℝ)*X 1 1+(2721961089/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132356499/250000000 : ℝ)*X 2 0+(217756883/400000000 : ℝ)*X 2 1+(-57097847/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4292196213/10000000000 : ℝ)*X 0 0+(4554138943/10000000000 : ℝ)*X 0 1+(126369313/312500000 : ℝ)*X 0 2+(4292196213/10000000000 : ℝ)*X 1 0+(4554138943/10000000000 : ℝ)*X 1 1+(126369313/312500000 : ℝ)*X 1 2+(4292196213/10000000000 : ℝ)*X 2 0+(4554138943/10000000000 : ℝ)*X 2 1+(126369313/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (936254933993464931951216757/192812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (872915297/100000000000000 : ℝ)*(base19) + (824067647/100000000000000 : ℝ)*(base23) + (16266039/50000000000000 : ℝ)*(lower2) + (122333263/100000000000000 : ℝ)*(upper3) + (42890801/50000000000000 : ℝ)*(upper5) + (773264590436437/25000000000000 : ℝ)*(major0) + (773264590436437/25000000000000 : ℝ)*(major1) + (773264590436437/25000000000000 : ℝ)*(major2) + (1061888319195331/25000000000000 : ℝ)*(sp0) + (42475652362229/1000000000000 : ℝ)*(sp1) + (84951305701411/2000000000000 : ℝ)*(sp2) + (969272113542767/50000000000000 : ℝ)*(sp3) + (6416178437/50000000000000 : ℝ)*(sp4) + (6225408447/100000000000000 : ℝ)*(sp7) + (96927522624699/5000000000000 : ℝ)*(f.failure) + (2123783054569099/50000000000000 : ℝ)*(f.sum) + (64472086970603/15425000000000000000000000000 : ℝ)*base66 + (3071550163140836081/771250000000000000000000000000000 : ℝ)*base67 + (201167851925413919/771250000000000000000000000000000 : ℝ)*base70 + (384031644920836081/771250000000000000000000000000000 : ℝ)*base71 + (37336217591653/15425000000000000000000000000 : ℝ)*base74 + (5297091892649586081/771250000000000000000000000000000 : ℝ)*base75 + (3546760726483336081/771250000000000000000000000000000 : ℝ)*base77 + (4431402519105836081/771250000000000000000000000000000 : ℝ)*base79 + (717606248579/482031250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (257501/31250000000000000000 : ℝ)*base90 + (257501/31250000000000000000 : ℝ)*base92 + (257501/31250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3137288273268358434865265709/771250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31450161/100000000000000 : ℝ)*(base19) + (563076207/100000000000000 : ℝ)*(base23) + (1317471/25000000000000 : ℝ)*(lower2) + (21829971/25000000000000 : ℝ)*(upper3) + (93686161/100000000000000 : ℝ)*(lower4) + (1563284562804377/50000000000000 : ℝ)*(major0) + (1563284562804377/50000000000000 : ℝ)*(major1) + (1563284562804377/50000000000000 : ℝ)*(major2) + (2548904213/25000000000000 : ℝ)*(sp2) + (291204827/100000000000000 : ℝ)*(sp3) + (4293585050553213/100000000000000 : ℝ)*(sp4) + (1073396254775763/25000000000000 : ℝ)*(sp5) + (2146787145930077/50000000000000 : ℝ)*(sp6) + (489888193466559/25000000000000 : ℝ)*(sp7) + (1959553065071063/100000000000000 : ℝ)*(f.failure) + (4293585050553213/100000000000000 : ℝ)*(f.sum) + (855224054009/964062500000000000000000000 : ℝ)*base66 + (15125831961396042699/1542500000000000000000000000000000 : ℝ)*base68 + (6298058191023542699/1542500000000000000000000000000000 : ℝ)*base70 + (8566375041248542699/1542500000000000000000000000000000 : ℝ)*base72 + (5134277000647/7712500000000000000000000000 : ℝ)*base74 + (5718811729983542699/1542500000000000000000000000000000 : ℝ)*base76 + (22317322601738542699/1542500000000000000000000000000000 : ℝ)*base78 + (8967300845318542699/1542500000000000000000000000000000 : ℝ)*base80 + (6871592510853/7712500000000000000000000000 : ℝ)*base81 + (7019663/625000000000000000000 : ℝ)*base89 + (7019663/625000000000000000000 : ℝ)*base91 + (7019663/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1464_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16209/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10039/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (663/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3897/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1464_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1464_s4_0 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1941207449/10000000000 : ℝ)*x 0 + (5440348549/10000000000 : ℝ)*x 1 + (2607051341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1941207449/10000000000 : ℝ)^4425 ≤ (11850018175977/100000000000000 : ℝ)^3401 := by
    have hnat : (1941207449 : ℕ)^4425*100000000000000^3401 ≤ 11850018175977^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941207449 10000000000 11850018175977 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440348549/10000000000 : ℝ)^4425 ≤ (4529258691371/10000000000000 : ℝ)^3401 := by
    have hnat : (5440348549 : ℕ)^4425*10000000000000^3401 ≤ 4529258691371^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440348549 10000000000 4529258691371 10000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607051341/5000000000 : ℝ)^4425 ≤ (42857394894333/100000000000000 : ℝ)^3401 := by
    have hnat : (2607051341 : ℕ)^4425*100000000000000^3401 ≤ 42857394894333^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607051341 5000000000 42857394894333 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1941207449/10000000000 : ℝ), (5440348549/10000000000 : ℝ), (2607051341/5000000000 : ℝ)] ![(11850018175977/100000000000000 : ℝ), (4529258691371/10000000000000 : ℝ), (42857394894333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1941207449/10000000000 : ℝ)|^4425 ≤ (11850018175977/100000000000000 : ℝ)^3401
        have hw : |(-1941207449/10000000000 : ℝ)|=(1941207449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440348549/10000000000 : ℝ)|^4425 ≤ (4529258691371/10000000000000 : ℝ)^3401
        have hw : |(5440348549/10000000000 : ℝ)|=(5440348549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607051341/5000000000 : ℝ)|^4425 ≤ (42857394894333/100000000000000 : ℝ)^3401
        have hw : |(2607051341/5000000000 : ℝ)|=(2607051341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s4_1 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354324643/10000000000 : ℝ)*x 0 + (-2057217717/10000000000 : ℝ)*x 1 + (5214102679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354324643/10000000000 : ℝ)^4425 ≤ (2218150287079/5000000000000 : ℝ)^3401 := by
    have hnat : (5354324643 : ℕ)^4425*5000000000000^3401 ≤ 2218150287079^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354324643 10000000000 2218150287079 5000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2057217717/10000000000 : ℝ)^4425 ≤ (2555919876531/20000000000000 : ℝ)^3401 := by
    have hnat : (2057217717 : ℕ)^4425*20000000000000^3401 ≤ 2555919876531^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057217717 10000000000 2555919876531 20000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214102679/10000000000 : ℝ)^4425 ≤ (171429579449/400000000000 : ℝ)^3401 := by
    have hnat : (5214102679 : ℕ)^4425*400000000000^3401 ≤ 171429579449^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214102679 10000000000 171429579449 400000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354324643/10000000000 : ℝ), (-2057217717/10000000000 : ℝ), (5214102679/10000000000 : ℝ)] ![(2218150287079/5000000000000 : ℝ), (2555919876531/20000000000000 : ℝ), (171429579449/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354324643/10000000000 : ℝ)|^4425 ≤ (2218150287079/5000000000000 : ℝ)^3401
        have hw : |(5354324643/10000000000 : ℝ)|=(5354324643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2057217717/10000000000 : ℝ)|^4425 ≤ (2555919876531/20000000000000 : ℝ)^3401
        have hw : |(-2057217717/10000000000 : ℝ)|=(2057217717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214102679/10000000000 : ℝ)|^4425 ≤ (171429579449/400000000000 : ℝ)^3401
        have hw : |(5214102679/10000000000 : ℝ)|=(5214102679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s4_2 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354324631/10000000000 : ℝ)*x 0 + (208564107/400000000 : ℝ)*x 1 + (-1028608869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354324631/10000000000 : ℝ)^4425 ≤ (22181502806109/50000000000000 : ℝ)^3401 := by
    have hnat : (5354324631 : ℕ)^4425*50000000000000^3401 ≤ 22181502806109^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354324631 10000000000 22181502806109 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208564107/400000000 : ℝ)^4425 ≤ (42857394819473/100000000000000 : ℝ)^3401 := by
    have hnat : (208564107 : ℕ)^4425*100000000000000^3401 ≤ 42857394819473^3401*400000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208564107 400000000 42857394819473 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028608869/5000000000 : ℝ)^4425 ≤ (12779599552387/100000000000000 : ℝ)^3401 := by
    have hnat : (1028608869 : ℕ)^4425*100000000000000^3401 ≤ 12779599552387^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028608869 5000000000 12779599552387 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354324631/10000000000 : ℝ), (208564107/400000000 : ℝ), (-1028608869/5000000000 : ℝ)] ![(22181502806109/50000000000000 : ℝ), (42857394819473/100000000000000 : ℝ), (12779599552387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354324631/10000000000 : ℝ)|^4425 ≤ (22181502806109/50000000000000 : ℝ)^3401
        have hw : |(5354324631/10000000000 : ℝ)|=(5354324631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208564107/400000000 : ℝ)|^4425 ≤ (42857394819473/100000000000000 : ℝ)^3401
        have hw : |(208564107/400000000 : ℝ)|=(208564107/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1028608869/5000000000 : ℝ)|^4425 ≤ (12779599552387/100000000000000 : ℝ)^3401
        have hw : |(-1028608869/5000000000 : ℝ)|=(1028608869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s4_3 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2146292941/5000000000 : ℝ)*x 0 + (4051048089/10000000000 : ℝ)*x 1 + (2273388279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146292941/5000000000 : ℝ)^4425 ≤ (8319076706909/25000000000000 : ℝ)^3401 := by
    have hnat : (2146292941 : ℕ)^4425*25000000000000^3401 ≤ 8319076706909^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146292941 5000000000 8319076706909 25000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4051048089/10000000000 : ℝ)^4425 ≤ (7715262261603/25000000000000 : ℝ)^3401 := by
    have hnat : (4051048089 : ℕ)^4425*25000000000000^3401 ≤ 7715262261603^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051048089 10000000000 7715262261603 25000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273388279/5000000000 : ℝ)^4425 ≤ (17931322054149/50000000000000 : ℝ)^3401 := by
    have hnat : (2273388279 : ℕ)^4425*50000000000000^3401 ≤ 17931322054149^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273388279 5000000000 17931322054149 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2146292941/5000000000 : ℝ), (4051048089/10000000000 : ℝ), (2273388279/5000000000 : ℝ)] ![(8319076706909/25000000000000 : ℝ), (7715262261603/25000000000000 : ℝ), (17931322054149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2146292941/5000000000 : ℝ)|^4425 ≤ (8319076706909/25000000000000 : ℝ)^3401
        have hw : |(2146292941/5000000000 : ℝ)|=(2146292941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4051048089/10000000000 : ℝ)|^4425 ≤ (7715262261603/25000000000000 : ℝ)^3401
        have hw : |(4051048089/10000000000 : ℝ)|=(4051048089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2273388279/5000000000 : ℝ)|^4425 ≤ (17931322054149/50000000000000 : ℝ)^3401
        have hw : |(2273388279/5000000000 : ℝ)|=(2273388279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s4_4 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-485309719/2500000000 : ℝ)*x 0 + (5215264823/10000000000 : ℝ)*x 1 + (679897257/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (485309719/2500000000 : ℝ)^4425 ≤ (5925133891757/50000000000000 : ℝ)^3401 := by
    have hnat : (485309719 : ℕ)^4425*50000000000000^3401 ≤ 5925133891757^3401*2500000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485309719 2500000000 5925133891757 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215264823/10000000000 : ℝ)^4425 ≤ (21434911804629/50000000000000 : ℝ)^3401 := by
    have hnat : (5215264823 : ℕ)^4425*50000000000000^3401 ≤ 21434911804629^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215264823 10000000000 21434911804629 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679897257/1250000000 : ℝ)^4425 ≤ (11319977147779/25000000000000 : ℝ)^3401 := by
    have hnat : (679897257 : ℕ)^4425*25000000000000^3401 ≤ 11319977147779^3401*1250000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679897257 1250000000 11319977147779 25000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-485309719/2500000000 : ℝ), (5215264823/10000000000 : ℝ), (679897257/1250000000 : ℝ)] ![(5925133891757/50000000000000 : ℝ), (21434911804629/50000000000000 : ℝ), (11319977147779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-485309719/2500000000 : ℝ)|^4425 ≤ (5925133891757/50000000000000 : ℝ)^3401
        have hw : |(-485309719/2500000000 : ℝ)|=(485309719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215264823/10000000000 : ℝ)|^4425 ≤ (21434911804629/50000000000000 : ℝ)^3401
        have hw : |(5215264823/10000000000 : ℝ)|=(5215264823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679897257/1250000000 : ℝ)|^4425 ≤ (11319977147779/25000000000000 : ℝ)^3401
        have hw : |(679897257/1250000000 : ℝ)|=(679897257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s4_5 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295403851/10000000000 : ℝ)*x 0 + (-366428441/2000000000 : ℝ)*x 1 + (135979459/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295403851/10000000000 : ℝ)^4425 ≤ (43728888500089/100000000000000 : ℝ)^3401 := by
    have hnat : (5295403851 : ℕ)^4425*100000000000000^3401 ≤ 43728888500089^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295403851 10000000000 43728888500089 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366428441/2000000000 : ℝ)^4425 ≤ (1373899950699/12500000000000 : ℝ)^3401 := by
    have hnat : (366428441 : ℕ)^4425*12500000000000^3401 ≤ 1373899950699^3401*2000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366428441 2000000000 1373899950699 12500000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135979459/250000000 : ℝ)^4425 ≤ (22639955941909/50000000000000 : ℝ)^3401 := by
    have hnat : (135979459 : ℕ)^4425*50000000000000^3401 ≤ 22639955941909^3401*250000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135979459 250000000 22639955941909 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295403851/10000000000 : ℝ), (-366428441/2000000000 : ℝ), (135979459/250000000 : ℝ)] ![(43728888500089/100000000000000 : ℝ), (1373899950699/12500000000000 : ℝ), (22639955941909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295403851/10000000000 : ℝ)|^4425 ≤ (43728888500089/100000000000000 : ℝ)^3401
        have hw : |(5295403851/10000000000 : ℝ)|=(5295403851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366428441/2000000000 : ℝ)|^4425 ≤ (1373899950699/12500000000000 : ℝ)^3401
        have hw : |(-366428441/2000000000 : ℝ)|=(366428441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135979459/250000000 : ℝ)|^4425 ≤ (22639955941909/50000000000000 : ℝ)^3401
        have hw : |(135979459/250000000 : ℝ)|=(135979459/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s4_6 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295404029/10000000000 : ℝ)*x 0 + (1359794649/2500000000 : ℝ)*x 1 + (-28627213/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295404029/10000000000 : ℝ)^4425 ≤ (8745778082513/20000000000000 : ℝ)^3401 := by
    have hnat : (5295404029 : ℕ)^4425*20000000000000^3401 ≤ 8745778082513^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295404029 10000000000 8745778082513 20000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359794649/2500000000 : ℝ)^4425 ≤ (9055982887999/20000000000000 : ℝ)^3401 := by
    have hnat : (1359794649 : ℕ)^4425*20000000000000^3401 ≤ 9055982887999^3401*2500000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359794649 2500000000 9055982887999 20000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28627213/156250000 : ℝ)^4425 ≤ (17585912213/160000000000 : ℝ)^3401 := by
    have hnat : (28627213 : ℕ)^4425*160000000000^3401 ≤ 17585912213^3401*156250000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28627213 156250000 17585912213 160000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295404029/10000000000 : ℝ), (1359794649/2500000000 : ℝ), (-28627213/156250000 : ℝ)] ![(8745778082513/20000000000000 : ℝ), (9055982887999/20000000000000 : ℝ), (17585912213/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295404029/10000000000 : ℝ)|^4425 ≤ (8745778082513/20000000000000 : ℝ)^3401
        have hw : |(5295404029/10000000000 : ℝ)|=(5295404029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359794649/2500000000 : ℝ)|^4425 ≤ (9055982887999/20000000000000 : ℝ)^3401
        have hw : |(1359794649/2500000000 : ℝ)|=(1359794649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28627213/156250000 : ℝ)|^4425 ≤ (17585912213/160000000000 : ℝ)^3401
        have hw : |(-28627213/156250000 : ℝ)|=(28627213/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s4_7 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4292655683/10000000000 : ℝ)*x 0 + (4544231137/10000000000 : ℝ)*x 1 + (2026806023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4292655683/10000000000 : ℝ)^4425 ≤ (1039906589013/3125000000000 : ℝ)^3401 := by
    have hnat : (4292655683 : ℕ)^4425*3125000000000^3401 ≤ 1039906589013^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4292655683 10000000000 1039906589013 3125000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4544231137/10000000000 : ℝ)^4425 ≤ (7167304879647/20000000000000 : ℝ)^3401 := by
    have hnat : (4544231137 : ℕ)^4425*20000000000000^3401 ≤ 7167304879647^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544231137 10000000000 7167304879647 20000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2026806023/5000000000 : ℝ)^4425 ≤ (123545858977/400000000000 : ℝ)^3401 := by
    have hnat : (2026806023 : ℕ)^4425*400000000000^3401 ≤ 123545858977^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026806023 5000000000 123545858977 400000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4292655683/10000000000 : ℝ), (4544231137/10000000000 : ℝ), (2026806023/5000000000 : ℝ)] ![(1039906589013/3125000000000 : ℝ), (7167304879647/20000000000000 : ℝ), (123545858977/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4292655683/10000000000 : ℝ)|^4425 ≤ (1039906589013/3125000000000 : ℝ)^3401
        have hw : |(4292655683/10000000000 : ℝ)|=(4292655683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4544231137/10000000000 : ℝ)|^4425 ≤ (7167304879647/20000000000000 : ℝ)^3401
        have hw : |(4544231137/10000000000 : ℝ)|=(4544231137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2026806023/5000000000 : ℝ)|^4425 ≤ (123545858977/400000000000 : ℝ)^3401
        have hw : |(2026806023/5000000000 : ℝ)|=(2026806023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1464_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3897/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (663/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (10701/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3897/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (663/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3897/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (663/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3897/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (663/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3897/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (663/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3897/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (663/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3897/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (663/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (663/6250 : ℝ) ^ (4423/1024 : ℝ) ≤ (309281406971131/5000000000000000000 : ℝ) := by
    have hpowers : (663/6250 : ℝ)^4423 ≤ (309281406971131/5000000000000000000 : ℝ)^1024 := by
      have hnat : (663 : ℕ)^4423*5000000000000000000^1024 ≤ 309281406971131^1024*6250^4423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        663 6250 309281406971131 5000000000000000000 4423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (663/6250 : ℝ)) (X := (309281406971131/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3897/25000 : ℝ) ^ (4423/1024 : ℝ) ≤ (32612985185842663/100000000000000000000 : ℝ) := by
    have hpowers : (3897/25000 : ℝ)^4423 ≤ (32612985185842663/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3897 : ℕ)^4423*100000000000000000000^1024 ≤ 32612985185842663^1024*25000^4423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3897 25000 32612985185842663 100000000000000000000 4423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3897/25000 : ℝ)) (X := (32612985185842663/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500309281406971131/2500000000000000000 : ℝ) ≤ (20000572804173/20000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (2500309281406971131/2500000000000000000 : ℝ)^1024 ≤ (20000572804173/20000000000000 : ℝ)^4423 := by
      have hnat : (2500309281406971131 : ℕ)^1024*20000000000000^4423 ≤ 20000572804173^4423*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500309281406971131 2500000000000000000 20000572804173 20000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20000572804173/20000000000000 : ℝ)) (X := (2500309281406971131/2500000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038798613325265283/100000000000000000000 : ℝ) ≤ (10000898120245749/10000000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (100038798613325265283/100000000000000000000 : ℝ)^1024 ≤ (10000898120245749/10000000000000000 : ℝ)^4423 := by
      have hnat : (100038798613325265283 : ℕ)^1024*10000000000000000^4423 ≤ 10000898120245749^4423*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038798613325265283 100000000000000000000 10000898120245749 10000000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000898120245749/10000000000000000 : ℝ)) (X := (100038798613325265283/100000000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032612985185842663/50000000000000000000 : ℝ) ≤ (5000754919202499/5000000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (50032612985185842663/50000000000000000000 : ℝ)^1024 ≤ (5000754919202499/5000000000000000 : ℝ)^4423 := by
      have hnat : (50032612985185842663 : ℕ)^1024*5000000000000000^4423 ≤ 5000754919202499^4423*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032612985185842663 50000000000000000000 5000754919202499 5000000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000754919202499/5000000000000000 : ℝ)) (X := (50032612985185842663/50000000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(309281406971131/5000000000000000000 : ℝ) ≤ ((1037259334790086317/1037500000000000000 : ℝ)+2*(203906053083/166000000000000 : ℝ)*(663/6250 : ℝ))^(4423/1024 : ℝ) := by
    rw [show (1037259334790086317/1037500000000000000 : ℝ)+2*(203906053083/166000000000000 : ℝ)*(663/6250 : ℝ)=(20000572804173/20000000000000 : ℝ) by norm_num, show 1+2*(309281406971131/5000000000000000000 : ℝ)=(2500309281406971131/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32612985185842663/100000000000000000000 : ℝ)+(309281406971131/5000000000000000000 : ℝ) ≤ ((1037259334790086317/1037500000000000000 : ℝ)+(203906053083/166000000000000 : ℝ)*((3897/25000 : ℝ)+(663/6250 : ℝ)))^(4423/1024 : ℝ) := by
    rw [show (1037259334790086317/1037500000000000000 : ℝ)+(203906053083/166000000000000 : ℝ)*((3897/25000 : ℝ)+(663/6250 : ℝ))=(10000898120245749/10000000000000000 : ℝ) by norm_num, show 1+(32612985185842663/100000000000000000000 : ℝ)+(309281406971131/5000000000000000000 : ℝ)=(100038798613325265283/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32612985185842663/100000000000000000000 : ℝ) ≤ ((1037259334790086317/1037500000000000000 : ℝ)+2*(203906053083/166000000000000 : ℝ)*(3897/25000 : ℝ))^(4423/1024 : ℝ) := by
    rw [show (1037259334790086317/1037500000000000000 : ℝ)+2*(203906053083/166000000000000 : ℝ)*(3897/25000 : ℝ)=(5000754919202499/5000000000000000 : ℝ) by norm_num, show 1+2*(32612985185842663/100000000000000000000 : ℝ)=(50032612985185842663/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1037259334790086317/1037500000000000000 : ℝ)*(X 1 0+X 2 0)+(203906053083/166000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (663/6250 : ℝ)) (hi := (3897/25000 : ℝ)) (c := (1037259334790086317/1037500000000000000 : ℝ)) (alpha := (203906053083/166000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1037259334790086317/1037500000000000000 : ℝ)*(X 0 1+X 2 1)+(203906053083/166000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (663/6250 : ℝ)) (hi := (3897/25000 : ℝ)) (c := (1037259334790086317/1037500000000000000 : ℝ)) (alpha := (203906053083/166000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1037259334790086317/1037500000000000000 : ℝ)*(X 0 2+X 1 2)+(203906053083/166000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (663/6250 : ℝ)) (hi := (3897/25000 : ℝ)) (c := (1037259334790086317/1037500000000000000 : ℝ)) (alpha := (203906053083/166000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1941207449/10000000000 : ℝ)*X 0 0+(5440348549/10000000000 : ℝ)*X 0 1+(2607051341/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354324643/10000000000 : ℝ)*X 1 0+(-2057217717/10000000000 : ℝ)*X 1 1+(5214102679/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354324631/10000000000 : ℝ)*X 2 0+(208564107/400000000 : ℝ)*X 2 1+(-1028608869/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2146292941/5000000000 : ℝ)*X 0 0+(4051048089/10000000000 : ℝ)*X 0 1+(2273388279/5000000000 : ℝ)*X 0 2+(2146292941/5000000000 : ℝ)*X 1 0+(4051048089/10000000000 : ℝ)*X 1 1+(2273388279/5000000000 : ℝ)*X 1 2+(2146292941/5000000000 : ℝ)*X 2 0+(4051048089/10000000000 : ℝ)*X 2 1+(2273388279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-485309719/2500000000 : ℝ)*X 0 0+(5215264823/10000000000 : ℝ)*X 0 1+(679897257/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295403851/10000000000 : ℝ)*X 1 0+(-366428441/2000000000 : ℝ)*X 1 1+(135979459/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295404029/10000000000 : ℝ)*X 2 0+(1359794649/2500000000 : ℝ)*X 2 1+(-28627213/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4292655683/10000000000 : ℝ)*X 0 0+(4544231137/10000000000 : ℝ)*X 0 1+(2026806023/5000000000 : ℝ)*X 0 2+(4292655683/10000000000 : ℝ)*X 1 0+(4544231137/10000000000 : ℝ)*X 1 1+(2026806023/5000000000 : ℝ)*X 1 2+(4292655683/10000000000 : ℝ)*X 2 0+(4544231137/10000000000 : ℝ)*X 2 1+(2026806023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (254094540354266207262594843/51875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (109348421/12500000000000 : ℝ)*(base19) + (415347913/50000000000000 : ℝ)*(base23) + (18304049/100000000000000 : ℝ)*(lower2) + (132620957/100000000000000 : ℝ)*(upper3) + (21521631/25000000000000 : ℝ)*(upper5) + (3218621356435831/100000000000000 : ℝ)*(major0) + (3218621356435831/100000000000000 : ℝ)*(major1) + (3218621356435831/100000000000000 : ℝ)*(major2) + (441998380955519/10000000000000 : ℝ)*(sp0) + (1104998896158051/25000000000000 : ℝ)*(sp1) + (2209997814361873/50000000000000 : ℝ)*(sp2) + (2017239401158099/100000000000000 : ℝ)*(sp3) + (12649864381/100000000000000 : ℝ)*(sp4) + (6689020383/100000000000000 : ℝ)*(sp7) + (1008623045089241/50000000000000 : ℝ)*(f.failure) + (1104999114854893/25000000000000 : ℝ)*(f.sum) + (6931600836673/8300000000000000000000000000 : ℝ)*base65 + (38189588263544323/103750000000000000000000000000000 : ℝ)*base68 + (448297010192294323/103750000000000000000000000000000 : ℝ)*base70 + (1238283571628544323/103750000000000000000000000000000 : ℝ)*base72 + (14016529899227/8300000000000000000000000000 : ℝ)*base74 + (1505388288692294323/103750000000000000000000000000000 : ℝ)*base76 + (442913719106044323/103750000000000000000000000000000 : ℝ)*base78 + (1973410499752294323/103750000000000000000000000000000 : ℝ)*base80 + (27967504372627/8300000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2314441/312500000000000000000 : ℝ)*base89 + (2314441/312500000000000000000 : ℝ)*base91 + (2314441/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78025822634053232628695037/6484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (720697743/50000000000000 : ℝ)*(base19) + (94750077/4000000000000 : ℝ)*(base23) + (185178577/50000000000000 : ℝ)*(upper3) + (256157587/100000000000000 : ℝ)*(lower4) + (61835371/100000000000000 : ℝ)*(upper5) + (3252124576828673/100000000000000 : ℝ)*(major0) + (3252124576828673/100000000000000 : ℝ)*(major1) + (3252124576828673/100000000000000 : ℝ)*(major2) + (18784977593/100000000000000 : ℝ)*(sp1) + (2258147593/5000000000000 : ℝ)*(sp2) + (558250597202109/12500000000000 : ℝ)*(sp4) + (279124034452737/6250000000000 : ℝ)*(sp5) + (2232978622956543/50000000000000 : ℝ)*(sp6) + (509560993735967/25000000000000 : ℝ)*(sp7) + (509560993735967/25000000000000 : ℝ)*(f.failure) + (558250597202109/12500000000000 : ℝ)*(f.sum) + (16226639118741/8300000000000000000000000000 : ℝ)*base66 + (206146703499063909/103750000000000000000000000000000 : ℝ)*base68 + (847392584254063909/103750000000000000000000000000000 : ℝ)*base70 + (260621425660313909/103750000000000000000000000000000 : ℝ)*base72 + (19890884963641/8300000000000000000000000000 : ℝ)*base74 + (1572527472510313909/103750000000000000000000000000000 : ℝ)*base76 + (294013638553436091/103750000000000000000000000000000 : ℝ)*base77 + (170543760124063909/103750000000000000000000000000000 : ℝ)*base80 + (48895928187941/8300000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2290867/156250000000000000000 : ℝ)*base89 + (2290867/156250000000000000000 : ℝ)*base91 + (2290867/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1464_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3897/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (663/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10701/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1464_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1464_s5_0 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1941313237/10000000000 : ℝ)*x 0 + (5439652319/10000000000 : ℝ)*x 1 + (2607364641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1941313237/10000000000 : ℝ)^4425 ≤ (740678649829/6250000000000 : ℝ)^3401 := by
    have hnat : (1941313237 : ℕ)^4425*6250000000000^3401 ≤ 740678649829^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941313237 10000000000 740678649829 6250000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439652319/10000000000 : ℝ)^4425 ≤ (45285045523547/100000000000000 : ℝ)^3401 := by
    have hnat : (5439652319 : ℕ)^4425*100000000000000^3401 ≤ 45285045523547^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439652319 10000000000 45285045523547 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607364641/5000000000 : ℝ)^4425 ≤ (2679006004449/6250000000000 : ℝ)^3401 := by
    have hnat : (2607364641 : ℕ)^4425*6250000000000^3401 ≤ 2679006004449^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607364641 5000000000 2679006004449 6250000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1941313237/10000000000 : ℝ), (5439652319/10000000000 : ℝ), (2607364641/5000000000 : ℝ)] ![(740678649829/6250000000000 : ℝ), (45285045523547/100000000000000 : ℝ), (2679006004449/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1941313237/10000000000 : ℝ)|^4425 ≤ (740678649829/6250000000000 : ℝ)^3401
        have hw : |(-1941313237/10000000000 : ℝ)|=(1941313237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439652319/10000000000 : ℝ)|^4425 ≤ (45285045523547/100000000000000 : ℝ)^3401
        have hw : |(5439652319/10000000000 : ℝ)|=(5439652319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607364641/5000000000 : ℝ)|^4425 ≤ (2679006004449/6250000000000 : ℝ)^3401
        have hw : |(2607364641/5000000000 : ℝ)|=(2607364641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s5_1 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354144811/10000000000 : ℝ)*x 0 + (-1028314231/5000000000 : ℝ)*x 1 + (325920579/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354144811/10000000000 : ℝ)^4425 ≤ (11090266785979/25000000000000 : ℝ)^3401 := by
    have hnat : (5354144811 : ℕ)^4425*25000000000000^3401 ≤ 11090266785979^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354144811 10000000000 11090266785979 25000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028314231/5000000000 : ℝ)^4425 ≤ (638741847869/5000000000000 : ℝ)^3401 := by
    have hnat : (1028314231 : ℕ)^4425*5000000000000^3401 ≤ 638741847869^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028314231 5000000000 638741847869 5000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325920579/625000000 : ℝ)^4425 ≤ (1071602396967/2500000000000 : ℝ)^3401 := by
    have hnat : (325920579 : ℕ)^4425*2500000000000^3401 ≤ 1071602396967^3401*625000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325920579 625000000 1071602396967 2500000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354144811/10000000000 : ℝ), (-1028314231/5000000000 : ℝ), (325920579/625000000 : ℝ)] ![(11090266785979/25000000000000 : ℝ), (638741847869/5000000000000 : ℝ), (1071602396967/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354144811/10000000000 : ℝ)|^4425 ≤ (11090266785979/25000000000000 : ℝ)^3401
        have hw : |(5354144811/10000000000 : ℝ)|=(5354144811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1028314231/5000000000 : ℝ)|^4425 ≤ (638741847869/5000000000000 : ℝ)^3401
        have hw : |(-1028314231/5000000000 : ℝ)|=(1028314231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(325920579/625000000 : ℝ)|^4425 ≤ (1071602396967/2500000000000 : ℝ)^3401
        have hw : |(325920579/625000000 : ℝ)|=(325920579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s5_2 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354144793/10000000000 : ℝ)*x 0 + (5214729293/10000000000 : ℝ)*x 1 + (-64269639/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354144793/10000000000 : ℝ)^4425 ≤ (11090266737469/25000000000000 : ℝ)^3401 := by
    have hnat : (5354144793 : ℕ)^4425*25000000000000^3401 ≤ 11090266737469^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354144793 10000000000 11090266737469 25000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214729293/10000000000 : ℝ)^4425 ≤ (21432048094413/50000000000000 : ℝ)^3401 := by
    have hnat : (5214729293 : ℕ)^4425*50000000000000^3401 ≤ 21432048094413^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214729293 10000000000 21432048094413 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64269639/312500000 : ℝ)^4425 ≤ (2554967368847/20000000000000 : ℝ)^3401 := by
    have hnat : (64269639 : ℕ)^4425*20000000000000^3401 ≤ 2554967368847^3401*312500000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64269639 312500000 2554967368847 20000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354144793/10000000000 : ℝ), (5214729293/10000000000 : ℝ), (-64269639/312500000 : ℝ)] ![(11090266737469/25000000000000 : ℝ), (21432048094413/50000000000000 : ℝ), (2554967368847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354144793/10000000000 : ℝ)|^4425 ≤ (11090266737469/25000000000000 : ℝ)^3401
        have hw : |(5354144793/10000000000 : ℝ)|=(5354144793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214729293/10000000000 : ℝ)|^4425 ≤ (21432048094413/50000000000000 : ℝ)^3401
        have hw : |(5214729293/10000000000 : ℝ)|=(5214729293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64269639/312500000 : ℝ)|^4425 ≤ (2554967368847/20000000000000 : ℝ)^3401
        have hw : |(-64269639/312500000 : ℝ)|=(64269639/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s5_3 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4292651773/10000000000 : ℝ)*x 0 + (2026244783/5000000000 : ℝ)*x 1 + (4545319419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4292651773/10000000000 : ℝ)^4425 ≤ (16638485705811/50000000000000 : ℝ)^3401 := by
    have hnat : (4292651773 : ℕ)^4425*50000000000000^3401 ≤ 16638485705811^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4292651773 10000000000 16638485705811 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2026244783/5000000000 : ℝ)^4425 ≤ (1543766867893/5000000000000 : ℝ)^3401 := by
    have hnat : (2026244783 : ℕ)^4425*5000000000000^3401 ≤ 1543766867893^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026244783 5000000000 1543766867893 5000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4545319419/10000000000 : ℝ)^4425 ≤ (35847691210519/100000000000000 : ℝ)^3401 := by
    have hnat : (4545319419 : ℕ)^4425*100000000000000^3401 ≤ 35847691210519^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4545319419 10000000000 35847691210519 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4292651773/10000000000 : ℝ), (2026244783/5000000000 : ℝ), (4545319419/10000000000 : ℝ)] ![(16638485705811/50000000000000 : ℝ), (1543766867893/5000000000000 : ℝ), (35847691210519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4292651773/10000000000 : ℝ)|^4425 ≤ (16638485705811/50000000000000 : ℝ)^3401
        have hw : |(4292651773/10000000000 : ℝ)|=(4292651773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2026244783/5000000000 : ℝ)|^4425 ≤ (1543766867893/5000000000000 : ℝ)^3401
        have hw : |(2026244783/5000000000 : ℝ)|=(2026244783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4545319419/10000000000 : ℝ)|^4425 ≤ (35847691210519/100000000000000 : ℝ)^3401
        have hw : |(4545319419/10000000000 : ℝ)|=(4545319419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s5_4 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1941344407/10000000000 : ℝ)*x 0 + (2607938719/5000000000 : ℝ)*x 1 + (679811967/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1941344407/10000000000 : ℝ)^4425 ≤ (11851105967647/100000000000000 : ℝ)^3401 := by
    have hnat : (1941344407 : ℕ)^4425*100000000000000^3401 ≤ 11851105967647^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941344407 10000000000 11851105967647 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607938719/5000000000 : ℝ)^4425 ≤ (21438187830207/50000000000000 : ℝ)^3401 := by
    have hnat : (2607938719 : ℕ)^4425*50000000000000^3401 ≤ 21438187830207^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607938719 5000000000 21438187830207 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679811967/1250000000 : ℝ)^4425 ≤ (22636259173299/50000000000000 : ℝ)^3401 := by
    have hnat : (679811967 : ℕ)^4425*50000000000000^3401 ≤ 22636259173299^3401*1250000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679811967 1250000000 22636259173299 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1941344407/10000000000 : ℝ), (2607938719/5000000000 : ℝ), (679811967/1250000000 : ℝ)] ![(11851105967647/100000000000000 : ℝ), (21438187830207/50000000000000 : ℝ), (22636259173299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1941344407/10000000000 : ℝ)|^4425 ≤ (11851105967647/100000000000000 : ℝ)^3401
        have hw : |(-1941344407/10000000000 : ℝ)|=(1941344407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607938719/5000000000 : ℝ)|^4425 ≤ (21438187830207/50000000000000 : ℝ)^3401
        have hw : |(2607938719/5000000000 : ℝ)|=(2607938719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679811967/1250000000 : ℝ)|^4425 ≤ (22636259173299/50000000000000 : ℝ)^3401
        have hw : |(679811967/1250000000 : ℝ)|=(679811967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s5_5 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647784529/5000000000 : ℝ)*x 0 + (-916430999/5000000000 : ℝ)*x 1 + (5438495729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647784529/5000000000 : ℝ)^4425 ≤ (8746132706657/20000000000000 : ℝ)^3401 := by
    have hnat : (2647784529 : ℕ)^4425*20000000000000^3401 ≤ 8746132706657^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647784529 5000000000 8746132706657 20000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (916430999/5000000000 : ℝ)^4425 ≤ (10996818176427/100000000000000 : ℝ)^3401 := by
    have hnat : (916430999 : ℕ)^4425*100000000000000^3401 ≤ 10996818176427^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916430999 5000000000 10996818176427 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438495729/10000000000 : ℝ)^4425 ≤ (22636259135391/50000000000000 : ℝ)^3401 := by
    have hnat : (5438495729 : ℕ)^4425*50000000000000^3401 ≤ 22636259135391^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438495729 10000000000 22636259135391 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647784529/5000000000 : ℝ), (-916430999/5000000000 : ℝ), (5438495729/10000000000 : ℝ)] ![(8746132706657/20000000000000 : ℝ), (10996818176427/100000000000000 : ℝ), (22636259135391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647784529/5000000000 : ℝ)|^4425 ≤ (8746132706657/20000000000000 : ℝ)^3401
        have hw : |(2647784529/5000000000 : ℝ)|=(2647784529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-916430999/5000000000 : ℝ)|^4425 ≤ (10996818176427/100000000000000 : ℝ)^3401
        have hw : |(-916430999/5000000000 : ℝ)|=(916430999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438495729/10000000000 : ℝ)|^4425 ≤ (22636259135391/50000000000000 : ℝ)^3401
        have hw : |(5438495729/10000000000 : ℝ)|=(5438495729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s5_6 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647784523/5000000000 : ℝ)*x 0 + (5438495739/10000000000 : ℝ)*x 1 + (-1832862001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647784523/5000000000 : ℝ)^4425 ≤ (683291615693/1562500000000 : ℝ)^3401 := by
    have hnat : (2647784523 : ℕ)^4425*1562500000000^3401 ≤ 683291615693^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647784523 5000000000 683291615693 1562500000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438495739/10000000000 : ℝ)^4425 ≤ (45272518379091/100000000000000 : ℝ)^3401 := by
    have hnat : (5438495739 : ℕ)^4425*100000000000000^3401 ≤ 45272518379091^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438495739 10000000000 45272518379091 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1832862001/10000000000 : ℝ)^4425 ≤ (5498409099923/50000000000000 : ℝ)^3401 := by
    have hnat : (1832862001 : ℕ)^4425*50000000000000^3401 ≤ 5498409099923^3401*10000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1832862001 10000000000 5498409099923 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647784523/5000000000 : ℝ), (5438495739/10000000000 : ℝ), (-1832862001/10000000000 : ℝ)] ![(683291615693/1562500000000 : ℝ), (45272518379091/100000000000000 : ℝ), (5498409099923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647784523/5000000000 : ℝ)|^4425 ≤ (683291615693/1562500000000 : ℝ)^3401
        have hw : |(2647784523/5000000000 : ℝ)|=(2647784523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438495739/10000000000 : ℝ)|^4425 ≤ (45272518379091/100000000000000 : ℝ)^3401
        have hw : |(5438495739/10000000000 : ℝ)|=(5438495739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1832862001/10000000000 : ℝ)|^4425 ≤ (5498409099923/50000000000000 : ℝ)^3401
        have hw : |(-1832862001/10000000000 : ℝ)|=(1832862001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1464_s5_7 (p : ℝ) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073180017/2500000000 : ℝ)*x 0 + (567850463/1250000000 : ℝ)*x 1 + (2027511893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073180017/2500000000 : ℝ)^4425 ≤ (33277660245863/100000000000000 : ℝ)^3401 := by
    have hnat : (1073180017 : ℕ)^4425*100000000000000^3401 ≤ 33277660245863^3401*2500000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073180017 2500000000 33277660245863 100000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (567850463/1250000000 : ℝ)^4425 ≤ (2238867424599/6250000000000 : ℝ)^3401 := by
    have hnat : (567850463 : ℕ)^4425*6250000000000^3401 ≤ 2238867424599^3401*1250000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567850463 1250000000 2238867424599 6250000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2027511893/5000000000 : ℝ)^4425 ≤ (15450230472301/50000000000000 : ℝ)^3401 := by
    have hnat : (2027511893 : ℕ)^4425*50000000000000^3401 ≤ 15450230472301^3401*5000000000^4425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027511893 5000000000 15450230472301 50000000000000 4425 3401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4425/1024 : ℝ)) 4425 3401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073180017/2500000000 : ℝ), (567850463/1250000000 : ℝ), (2027511893/5000000000 : ℝ)] ![(33277660245863/100000000000000 : ℝ), (2238867424599/6250000000000 : ℝ), (15450230472301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073180017/2500000000 : ℝ)|^4425 ≤ (33277660245863/100000000000000 : ℝ)^3401
        have hw : |(1073180017/2500000000 : ℝ)|=(1073180017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(567850463/1250000000 : ℝ)|^4425 ≤ (2238867424599/6250000000000 : ℝ)^3401
        have hw : |(567850463/1250000000 : ℝ)|=(567850463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2027511893/5000000000 : ℝ)|^4425 ≤ (15450230472301/50000000000000 : ℝ)^3401
        have hw : |(2027511893/5000000000 : ℝ)|=(2027511893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1464_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10701/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5357/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15473/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10701/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10701/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10701/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10701/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10701/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10701/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10701/100000 : ℝ) ^ (4423/1024 : ℝ) ≤ (401455851975367/6250000000000000000 : ℝ) := by
    have hpowers : (10701/100000 : ℝ)^4423 ≤ (401455851975367/6250000000000000000 : ℝ)^1024 := by
      have hnat : (10701 : ℕ)^4423*6250000000000000000^1024 ≤ 401455851975367^1024*100000^4423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10701 100000 401455851975367 6250000000000000000 4423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10701/100000 : ℝ)) (X := (401455851975367/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4423/1024 : ℝ) ≤ (31718874045727391/100000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4423 ≤ (31718874045727391/100000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4423*100000000000000000000^1024 ≤ 31718874045727391^1024*3125^4423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 31718874045727391 100000000000000000000 4423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (31718874045727391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125401455851975367/3125000000000000000 : ℝ) ≤ (10000297405743961/10000000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (3125401455851975367/3125000000000000000 : ℝ)^1024 ≤ (10000297405743961/10000000000000000 : ℝ)^4423 := by
      have hnat : (3125401455851975367 : ℕ)^1024*10000000000000000^4423 ≤ 10000297405743961^4423*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125401455851975367 3125000000000000000 10000297405743961 10000000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000297405743961/10000000000000000 : ℝ)) (X := (3125401455851975367/3125000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038142167677333263/100000000000000000000 : ℝ) ≤ (1250110365862499/1250000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (100038142167677333263/100000000000000000000 : ℝ)^1024 ≤ (1250110365862499/1250000000000000 : ℝ)^4423 := by
      have hnat : (100038142167677333263 : ℕ)^1024*1250000000000000^4423 ≤ 1250110365862499^4423*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038142167677333263 100000000000000000000 1250110365862499 1250000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250110365862499/1250000000000000 : ℝ)) (X := (100038142167677333263/100000000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031718874045727391/50000000000000000000 : ℝ) ≤ (10001468448056023/10000000000000000 : ℝ) ^ (4423/1024 : ℝ) := by
    have hpowers : (50031718874045727391/50000000000000000000 : ℝ)^1024 ≤ (10001468448056023/10000000000000000 : ℝ)^4423 := by
      have hnat : (50031718874045727391 : ℕ)^1024*10000000000000000^4423 ≤ 10001468448056023^4423*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031718874045727391 50000000000000000000 10001468448056023 10000000000000000 1024 4423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001468448056023/10000000000000000 : ℝ)) (X := (50031718874045727391/50000000000000000000 : ℝ)) (by norm_num) 4423 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(401455851975367/6250000000000000000 : ℝ) ≤ ((9571778471502993169/9574000000000000000 : ℝ)+2*(585521156031/478700000000000 : ℝ)*(10701/100000 : ℝ))^(4423/1024 : ℝ) := by
    rw [show (9571778471502993169/9574000000000000000 : ℝ)+2*(585521156031/478700000000000 : ℝ)*(10701/100000 : ℝ)=(10000297405743961/10000000000000000 : ℝ) by norm_num, show 1+2*(401455851975367/6250000000000000000 : ℝ)=(3125401455851975367/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31718874045727391/100000000000000000000 : ℝ)+(401455851975367/6250000000000000000 : ℝ) ≤ ((9571778471502993169/9574000000000000000 : ℝ)+(585521156031/478700000000000 : ℝ)*((484/3125 : ℝ)+(10701/100000 : ℝ)))^(4423/1024 : ℝ) := by
    rw [show (9571778471502993169/9574000000000000000 : ℝ)+(585521156031/478700000000000 : ℝ)*((484/3125 : ℝ)+(10701/100000 : ℝ))=(1250110365862499/1250000000000000 : ℝ) by norm_num, show 1+(31718874045727391/100000000000000000000 : ℝ)+(401455851975367/6250000000000000000 : ℝ)=(100038142167677333263/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31718874045727391/100000000000000000000 : ℝ) ≤ ((9571778471502993169/9574000000000000000 : ℝ)+2*(585521156031/478700000000000 : ℝ)*(484/3125 : ℝ))^(4423/1024 : ℝ) := by
    rw [show (9571778471502993169/9574000000000000000 : ℝ)+2*(585521156031/478700000000000 : ℝ)*(484/3125 : ℝ)=(10001468448056023/10000000000000000 : ℝ) by norm_num, show 1+2*(31718874045727391/100000000000000000000 : ℝ)=(50031718874045727391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9571778471502993169/9574000000000000000 : ℝ)*(X 1 0+X 2 0)+(585521156031/478700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (10701/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (9571778471502993169/9574000000000000000 : ℝ)) (alpha := (585521156031/478700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9571778471502993169/9574000000000000000 : ℝ)*(X 0 1+X 2 1)+(585521156031/478700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (10701/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (9571778471502993169/9574000000000000000 : ℝ)) (alpha := (585521156031/478700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9571778471502993169/9574000000000000000 : ℝ)*(X 0 2+X 1 2)+(585521156031/478700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4423/1024 : ℝ)) (lo := (10701/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (9571778471502993169/9574000000000000000 : ℝ)) (alpha := (585521156031/478700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1941313237/10000000000 : ℝ)*X 0 0+(5439652319/10000000000 : ℝ)*X 0 1+(2607364641/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354144811/10000000000 : ℝ)*X 1 0+(-1028314231/5000000000 : ℝ)*X 1 1+(325920579/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354144793/10000000000 : ℝ)*X 2 0+(5214729293/10000000000 : ℝ)*X 2 1+(-64269639/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4292651773/10000000000 : ℝ)*X 0 0+(2026244783/5000000000 : ℝ)*X 0 1+(4545319419/10000000000 : ℝ)*X 0 2+(4292651773/10000000000 : ℝ)*X 1 0+(2026244783/5000000000 : ℝ)*X 1 1+(4545319419/10000000000 : ℝ)*X 1 2+(4292651773/10000000000 : ℝ)*X 2 0+(2026244783/5000000000 : ℝ)*X 2 1+(4545319419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1941344407/10000000000 : ℝ)*X 0 0+(2607938719/5000000000 : ℝ)*X 0 1+(679811967/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647784529/5000000000 : ℝ)*X 1 0+(-916430999/5000000000 : ℝ)*X 1 1+(5438495729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647784523/5000000000 : ℝ)*X 2 0+(5438495739/10000000000 : ℝ)*X 2 1+(-1832862001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1073180017/2500000000 : ℝ)*X 0 0+(567850463/1250000000 : ℝ)*X 0 1+(2027511893/5000000000 : ℝ)*X 0 2+(1073180017/2500000000 : ℝ)*X 1 0+(567850463/1250000000 : ℝ)*X 1 1+(2027511893/5000000000 : ℝ)*X 1 2+(1073180017/2500000000 : ℝ)*X 2 0+(567850463/1250000000 : ℝ)*X 2 1+(2027511893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1464_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1066527060843913072662295371/119675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (164414263/10000000000000 : ℝ)*(base19) + (1517543743/100000000000000 : ℝ)*(base23) + (59780051/100000000000000 : ℝ)*(lower2) + (112274859/50000000000000 : ℝ)*(upper3) + (19031129/12500000000000 : ℝ)*(upper5) + (809392117755149/25000000000000 : ℝ)*(major0) + (809392117755149/25000000000000 : ℝ)*(major1) + (809392117755149/25000000000000 : ℝ)*(major2) + (2222995414730457/50000000000000 : ℝ)*(sp0) + (2223006976423657/50000000000000 : ℝ)*(sp1) + (2223007039723101/50000000000000 : ℝ)*(sp2) + (40582177179143/2000000000000 : ℝ)*(sp3) + (2476752903/10000000000000 : ℝ)*(sp4) + (12189032027/100000000000000 : ℝ)*(sp7) + (1014560523994589/50000000000000 : ℝ)*(f.failure) + (555751949623743/12500000000000 : ℝ)*(f.sum) + (49330352517373/11967500000000000000000000000 : ℝ)*base65 + (1991904314523057181/239350000000000000000000000000000 : ℝ)*base67 + (2538919523068957181/239350000000000000000000000000000 : ℝ)*base69 + (4176087276119957181/239350000000000000000000000000000 : ℝ)*base71 + (7530288186481/5983750000000000000000000000 : ℝ)*base74 + (859137989843157181/239350000000000000000000000000000 : ℝ)*base75 + (386329828485757181/239350000000000000000000000000000 : ℝ)*base77 + (3944997806135057181/239350000000000000000000000000000 : ℝ)*base79 + (63483290650729/5983750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1920389/312500000000000000000 : ℝ)*base89 + (1920389/312500000000000000000 : ℝ)*base91 + (1920389/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (398017532019412601183722383/59837500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1121382599/100000000000000 : ℝ)*(base19) + (60475623/5000000000000 : ℝ)*(base23) + (68681319/50000000000000 : ℝ)*(upper3) + (22408757/50000000000000 : ℝ)*(lower4) + (68306399/50000000000000 : ℝ)*(upper5) + (817762226292231/25000000000000 : ℝ)*(major0) + (817762226292231/25000000000000 : ℝ)*(major1) + (817762226292231/25000000000000 : ℝ)*(major2) + (829016357/5000000000000 : ℝ)*(sp1) + (17816788149/100000000000000 : ℝ)*(sp2) + (4491992936964793/100000000000000 : ℝ)*(sp4) + (2245987617627527/50000000000000 : ℝ)*(sp5) + (561496738833023/12500000000000 : ℝ)*(sp6) + (256263081456463/12500000000000 : ℝ)*(sp7) + (256263081456463/12500000000000 : ℝ)*(f.failure) + (4491992936964793/100000000000000 : ℝ)*(f.sum) + (85232830870491/23935000000000000000000000000 : ℝ)*base66 + (1147709078061490039/239350000000000000000000000000000 : ℝ)*base67 + (1409817965691209961/239350000000000000000000000000000 : ℝ)*base70 + (1579153347337590039/239350000000000000000000000000000 : ℝ)*base71 + (12445319537813/2991875000000000000000000000 : ℝ)*base73 + (614253284929490039/239350000000000000000000000000000 : ℝ)*base75 + (1093340595594440039/239350000000000000000000000000000 : ℝ)*base77 + (1363023479495840039/239350000000000000000000000000000 : ℝ)*base79 + (12325182536209/5983750000000000000000000000 : ℝ)*base82 + (89937/78125000000000000000 : ℝ)*base90 + (89937/78125000000000000000 : ℝ)*base92 + (89937/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1464_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10701/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1464_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1464_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16209/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10039/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1464_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1464_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1464_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4423/1024 : ℝ) ≤ p) (hpb : p ≤ (4425/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9972201/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16209/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10039/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1464_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
