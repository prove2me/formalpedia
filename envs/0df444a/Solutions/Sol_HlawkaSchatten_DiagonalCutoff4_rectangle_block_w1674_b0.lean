-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1674_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:27:18.510399+00:00
-- url     : https://prove2.me/submissions/00770a59-5bea-44b6-ae4c-74fb1f62f635

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
theorem support_rectangle_w1674_s0_0 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1451457887/10000000000 : ℝ)*x 0 + (719543199/1250000000 : ℝ)*x 1 + (1234345297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1451457887/10000000000 : ℝ)^5015 ≤ (8845909394993/100000000000000 : ℝ)^3991 := by
    have hnat : (1451457887 : ℕ)^5015*100000000000000^3991 ≤ 8845909394993^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1451457887 10000000000 8845909394993 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (719543199/1250000000 : ℝ)^5015 ≤ (49958108717527/100000000000000 : ℝ)^3991 := by
    have hnat : (719543199 : ℕ)^5015*100000000000000^3991 ≤ 49958108717527^3991*1250000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719543199 1250000000 49958108717527 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1234345297/2500000000 : ℝ)^5015 ≤ (20597990937491/50000000000000 : ℝ)^3991 := by
    have hnat : (1234345297 : ℕ)^5015*50000000000000^3991 ≤ 20597990937491^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234345297 2500000000 20597990937491 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1451457887/10000000000 : ℝ), (719543199/1250000000 : ℝ), (1234345297/2500000000 : ℝ)] ![(8845909394993/100000000000000 : ℝ), (49958108717527/100000000000000 : ℝ), (20597990937491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1451457887/10000000000 : ℝ)|^5015 ≤ (8845909394993/100000000000000 : ℝ)^3991
        have hw : |(-1451457887/10000000000 : ℝ)|=(1451457887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(719543199/1250000000 : ℝ)|^5015 ≤ (49958108717527/100000000000000 : ℝ)^3991
        have hw : |(719543199/1250000000 : ℝ)|=(719543199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1234345297/2500000000 : ℝ)|^5015 ≤ (20597990937491/50000000000000 : ℝ)^3991
        have hw : |(1234345297/2500000000 : ℝ)|=(1234345297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s0_1 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5428140657/10000000000 : ℝ)*x 0 + (-1898866943/10000000000 : ℝ)*x 1 + (4937382343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5428140657/10000000000 : ℝ)^5015 ≤ (9281081419629/20000000000000 : ℝ)^3991 := by
    have hnat : (5428140657 : ℕ)^5015*20000000000000^3991 ≤ 9281081419629^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428140657 10000000000 9281081419629 20000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1898866943/10000000000 : ℝ)^5015 ≤ (12398598893613/100000000000000 : ℝ)^3991 := by
    have hnat : (1898866943 : ℕ)^5015*100000000000000^3991 ≤ 12398598893613^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898866943 10000000000 12398598893613 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4937382343/10000000000 : ℝ)^5015 ≤ (41195993984571/100000000000000 : ℝ)^3991 := by
    have hnat : (4937382343 : ℕ)^5015*100000000000000^3991 ≤ 41195993984571^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4937382343 10000000000 41195993984571 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5428140657/10000000000 : ℝ), (-1898866943/10000000000 : ℝ), (4937382343/10000000000 : ℝ)] ![(9281081419629/20000000000000 : ℝ), (12398598893613/100000000000000 : ℝ), (41195993984571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5428140657/10000000000 : ℝ)|^5015 ≤ (9281081419629/20000000000000 : ℝ)^3991
        have hw : |(5428140657/10000000000 : ℝ)|=(5428140657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1898866943/10000000000 : ℝ)|^5015 ≤ (12398598893613/100000000000000 : ℝ)^3991
        have hw : |(-1898866943/10000000000 : ℝ)|=(1898866943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4937382343/10000000000 : ℝ)|^5015 ≤ (41195993984571/100000000000000 : ℝ)^3991
        have hw : |(4937382343/10000000000 : ℝ)|=(4937382343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s0_2 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (542814337/1000000000 : ℝ)*x 0 + (197495231/400000000 : ℝ)*x 1 + (-474716349/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542814337/1000000000 : ℝ)^5015 ≤ (580067953033/1250000000000 : ℝ)^3991 := by
    have hnat : (542814337 : ℕ)^5015*1250000000000^3991 ≤ 580067953033^3991*1000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542814337 1000000000 580067953033 1250000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197495231/400000000 : ℝ)^5015 ≤ (20597988772443/50000000000000 : ℝ)^3991 := by
    have hnat : (197495231 : ℕ)^5015*50000000000000^3991 ≤ 20597988772443^3991*400000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197495231 400000000 20597988772443 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (474716349/2500000000 : ℝ)^5015 ≤ (1239858620081/10000000000000 : ℝ)^3991 := by
    have hnat : (474716349 : ℕ)^5015*10000000000000^3991 ≤ 1239858620081^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474716349 2500000000 1239858620081 10000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542814337/1000000000 : ℝ), (197495231/400000000 : ℝ), (-474716349/2500000000 : ℝ)] ![(580067953033/1250000000000 : ℝ), (20597988772443/50000000000000 : ℝ), (1239858620081/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542814337/1000000000 : ℝ)|^5015 ≤ (580067953033/1250000000000 : ℝ)^3991
        have hw : |(542814337/1000000000 : ℝ)|=(542814337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(197495231/400000000 : ℝ)|^5015 ≤ (20597988772443/50000000000000 : ℝ)^3991
        have hw : |(197495231/400000000 : ℝ)|=(197495231/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-474716349/2500000000 : ℝ)|^5015 ≤ (1239858620081/10000000000000 : ℝ)^3991
        have hw : |(-474716349/2500000000 : ℝ)|=(474716349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s0_3 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2039761313/5000000000 : ℝ)*x 0 + (3089091961/10000000000 : ℝ)*x 1 + (2636076731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2039761313/5000000000 : ℝ)^5015 ≤ (3241160548241/10000000000000 : ℝ)^3991 := by
    have hnat : (2039761313 : ℕ)^5015*10000000000000^3991 ≤ 3241160548241^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039761313 5000000000 3241160548241 10000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3089091961/10000000000 : ℝ)^5015 ≤ (11426231422039/50000000000000 : ℝ)^3991 := by
    have hnat : (3089091961 : ℕ)^5015*50000000000000^3991 ≤ 11426231422039^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3089091961 10000000000 11426231422039 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636076731/5000000000 : ℝ)^5015 ≤ (44735931660129/100000000000000 : ℝ)^3991 := by
    have hnat : (2636076731 : ℕ)^5015*100000000000000^3991 ≤ 44735931660129^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636076731 5000000000 44735931660129 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2039761313/5000000000 : ℝ), (3089091961/10000000000 : ℝ), (2636076731/5000000000 : ℝ)] ![(3241160548241/10000000000000 : ℝ), (11426231422039/50000000000000 : ℝ), (44735931660129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2039761313/5000000000 : ℝ)|^5015 ≤ (3241160548241/10000000000000 : ℝ)^3991
        have hw : |(2039761313/5000000000 : ℝ)|=(2039761313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3089091961/10000000000 : ℝ)|^5015 ≤ (11426231422039/50000000000000 : ℝ)^3991
        have hw : |(3089091961/10000000000 : ℝ)|=(3089091961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636076731/5000000000 : ℝ)|^5015 ≤ (44735931660129/100000000000000 : ℝ)^3991
        have hw : |(2636076731/5000000000 : ℝ)|=(2636076731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s0_4 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-290699717/2000000000 : ℝ)*x 0 + (2478713941/5000000000 : ℝ)*x 1 + (5735620017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (290699717/2000000000 : ℝ)^5015 ≤ (2215385076537/25000000000000 : ℝ)^3991 := by
    have hnat : (290699717 : ℕ)^5015*25000000000000^3991 ≤ 2215385076537^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290699717 2000000000 2215385076537 25000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2478713941/5000000000 : ℝ)^5015 ≤ (20703135326843/50000000000000 : ℝ)^3991 := by
    have hnat : (2478713941 : ℕ)^5015*50000000000000^3991 ≤ 20703135326843^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2478713941 5000000000 20703135326843 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5735620017/10000000000 : ℝ)^5015 ≤ (49732189018597/100000000000000 : ℝ)^3991 := by
    have hnat : (5735620017 : ℕ)^5015*100000000000000^3991 ≤ 49732189018597^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5735620017 10000000000 49732189018597 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-290699717/2000000000 : ℝ), (2478713941/5000000000 : ℝ), (5735620017/10000000000 : ℝ)] ![(2215385076537/25000000000000 : ℝ), (20703135326843/50000000000000 : ℝ), (49732189018597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-290699717/2000000000 : ℝ)|^5015 ≤ (2215385076537/25000000000000 : ℝ)^3991
        have hw : |(-290699717/2000000000 : ℝ)|=(290699717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2478713941/5000000000 : ℝ)|^5015 ≤ (20703135326843/50000000000000 : ℝ)^3991
        have hw : |(2478713941/5000000000 : ℝ)|=(2478713941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5735620017/10000000000 : ℝ)|^5015 ≤ (49732189018597/100000000000000 : ℝ)^3991
        have hw : |(5735620017/10000000000 : ℝ)|=(5735620017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s0_5 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1301217839/2500000000 : ℝ)*x 0 + (-1100628453/10000000000 : ℝ)*x 1 + (716952513/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1301217839/2500000000 : ℝ)^5015 ≤ (8803943349889/20000000000000 : ℝ)^3991 := by
    have hnat : (1301217839 : ℕ)^5015*20000000000000^3991 ≤ 8803943349889^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301217839 2500000000 8803943349889 20000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100628453/10000000000 : ℝ)^5015 ≤ (6248093276713/100000000000000 : ℝ)^3991 := by
    have hnat : (1100628453 : ℕ)^5015*100000000000000^3991 ≤ 6248093276713^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100628453 10000000000 6248093276713 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (716952513/1250000000 : ℝ)^5015 ≤ (49732189966503/100000000000000 : ℝ)^3991 := by
    have hnat : (716952513 : ℕ)^5015*100000000000000^3991 ≤ 49732189966503^3991*1250000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716952513 1250000000 49732189966503 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1301217839/2500000000 : ℝ), (-1100628453/10000000000 : ℝ), (716952513/1250000000 : ℝ)] ![(8803943349889/20000000000000 : ℝ), (6248093276713/100000000000000 : ℝ), (49732189966503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1301217839/2500000000 : ℝ)|^5015 ≤ (8803943349889/20000000000000 : ℝ)^3991
        have hw : |(1301217839/2500000000 : ℝ)|=(1301217839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1100628453/10000000000 : ℝ)|^5015 ≤ (6248093276713/100000000000000 : ℝ)^3991
        have hw : |(-1100628453/10000000000 : ℝ)|=(1100628453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(716952513/1250000000 : ℝ)|^5015 ≤ (49732189966503/100000000000000 : ℝ)^3991
        have hw : |(716952513/1250000000 : ℝ)|=(716952513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s0_6 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5204871357/10000000000 : ℝ)*x 0 + (1147124011/2000000000 : ℝ)*x 1 + (-44025141/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5204871357/10000000000 : ℝ)^5015 ≤ (5502464595009/12500000000000 : ℝ)^3991 := by
    have hnat : (5204871357 : ℕ)^5015*12500000000000^3991 ≤ 5502464595009^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204871357 10000000000 5502464595009 12500000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1147124011/2000000000 : ℝ)^5015 ≤ (397857515461/800000000000 : ℝ)^3991 := by
    have hnat : (1147124011 : ℕ)^5015*800000000000^3991 ≤ 397857515461^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147124011 2000000000 397857515461 800000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44025141/400000000 : ℝ)^5015 ≤ (6248093790317/100000000000000 : ℝ)^3991 := by
    have hnat : (44025141 : ℕ)^5015*100000000000000^3991 ≤ 6248093790317^3991*400000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44025141 400000000 6248093790317 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5204871357/10000000000 : ℝ), (1147124011/2000000000 : ℝ), (-44025141/400000000 : ℝ)] ![(5502464595009/12500000000000 : ℝ), (397857515461/800000000000 : ℝ), (6248093790317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5204871357/10000000000 : ℝ)|^5015 ≤ (5502464595009/12500000000000 : ℝ)^3991
        have hw : |(5204871357/10000000000 : ℝ)|=(5204871357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1147124011/2000000000 : ℝ)|^5015 ≤ (397857515461/800000000000 : ℝ)^3991
        have hw : |(1147124011/2000000000 : ℝ)|=(1147124011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44025141/400000000 : ℝ)|^5015 ≤ (6248093790317/100000000000000 : ℝ)^3991
        have hw : |(-44025141/400000000 : ℝ)|=(44025141/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s0_7 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4084961377/10000000000 : ℝ)*x 0 + (5218714483/10000000000 : ℝ)*x 1 + (628867751/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4084961377/10000000000 : ℝ)^5015 ≤ (8116478058663/25000000000000 : ℝ)^3991 := by
    have hnat : (4084961377 : ℕ)^5015*25000000000000^3991 ≤ 8116478058663^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4084961377 10000000000 8116478058663 25000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218714483/10000000000 : ℝ)^5015 ≤ (22083441583191/50000000000000 : ℝ)^3991 := by
    have hnat : (5218714483 : ℕ)^5015*50000000000000^3991 ≤ 22083441583191^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218714483 10000000000 22083441583191 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628867751/2000000000 : ℝ)^5015 ≤ (5841801145871/25000000000000 : ℝ)^3991 := by
    have hnat : (628867751 : ℕ)^5015*25000000000000^3991 ≤ 5841801145871^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628867751 2000000000 5841801145871 25000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4084961377/10000000000 : ℝ), (5218714483/10000000000 : ℝ), (628867751/2000000000 : ℝ)] ![(8116478058663/25000000000000 : ℝ), (22083441583191/50000000000000 : ℝ), (5841801145871/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4084961377/10000000000 : ℝ)|^5015 ≤ (8116478058663/25000000000000 : ℝ)^3991
        have hw : |(4084961377/10000000000 : ℝ)|=(4084961377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218714483/10000000000 : ℝ)|^5015 ≤ (22083441583191/50000000000000 : ℝ)^3991
        have hw : |(5218714483/10000000000 : ℝ)|=(5218714483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628867751/2000000000 : ℝ)|^5015 ≤ (5841801145871/25000000000000 : ℝ)^3991
        have hw : |(628867751/2000000000 : ℝ)|=(628867751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1674_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5293/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (22859/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5011/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5011 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5011*1^1024 ≤ 0^1024*1^5011 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5011 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5011/1024 : ℝ) ≤ (56445433083100921/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5011 ≤ (56445433083100921/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5011*5000000000000000000^1024 ≤ 56445433083100921^1024*5^5011 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 56445433083100921 5000000000000000000 5011 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (56445433083100921/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5011 := by
      have hnat : (1 : ℕ)^1024*1^5011 ≤ 1^5011*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5056445433083100921/5000000000000000000 : ℝ) ≤ (5011483192756277/5000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (5056445433083100921/5000000000000000000 : ℝ)^1024 ≤ (5011483192756277/5000000000000000 : ℝ)^5011 := by
      have hnat : (5056445433083100921 : ℕ)^1024*5000000000000000^5011 ≤ 5011483192756277^5011*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5056445433083100921 5000000000000000000 5011483192756277 5000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011483192756277/5000000000000000 : ℝ)) (X := (5056445433083100921/5000000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2556445433083100921/2500000000000000000 : ℝ) ≤ (2511483192756277/2500000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (2556445433083100921/2500000000000000000 : ℝ)^1024 ≤ (2511483192756277/2500000000000000 : ℝ)^5011 := by
      have hnat : (2556445433083100921 : ℕ)^1024*2500000000000000^5011 ≤ 2511483192756277^5011*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2556445433083100921 2500000000000000000 2511483192756277 2500000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511483192756277/2500000000000000 : ℝ)) (X := (2556445433083100921/2500000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11483192756277/2000000000000000 : ℝ)*(0 : ℝ))^(5011/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11483192756277/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(56445433083100921/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11483192756277/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5011/1024 : ℝ) := by
    rw [show (1 : ℝ)+(11483192756277/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5011483192756277/5000000000000000 : ℝ) by norm_num, show 1+(56445433083100921/5000000000000000000 : ℝ)+(0 : ℝ)=(5056445433083100921/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(56445433083100921/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11483192756277/2000000000000000 : ℝ)*(2/5 : ℝ))^(5011/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11483192756277/2000000000000000 : ℝ)*(2/5 : ℝ)=(2511483192756277/2500000000000000 : ℝ) by norm_num, show 1+2*(56445433083100921/5000000000000000000 : ℝ)=(2556445433083100921/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11483192756277/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11483192756277/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11483192756277/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11483192756277/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11483192756277/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11483192756277/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1451457887/10000000000 : ℝ)*X 0 0+(719543199/1250000000 : ℝ)*X 0 1+(1234345297/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5428140657/10000000000 : ℝ)*X 1 0+(-1898866943/10000000000 : ℝ)*X 1 1+(4937382343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((542814337/1000000000 : ℝ)*X 2 0+(197495231/400000000 : ℝ)*X 2 1+(-474716349/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2039761313/5000000000 : ℝ)*X 0 0+(3089091961/10000000000 : ℝ)*X 0 1+(2636076731/5000000000 : ℝ)*X 0 2+(2039761313/5000000000 : ℝ)*X 1 0+(3089091961/10000000000 : ℝ)*X 1 1+(2636076731/5000000000 : ℝ)*X 1 2+(2039761313/5000000000 : ℝ)*X 2 0+(3089091961/10000000000 : ℝ)*X 2 1+(2636076731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-290699717/2000000000 : ℝ)*X 0 0+(2478713941/5000000000 : ℝ)*X 0 1+(5735620017/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1301217839/2500000000 : ℝ)*X 1 0+(-1100628453/10000000000 : ℝ)*X 1 1+(716952513/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5204871357/10000000000 : ℝ)*X 2 0+(1147124011/2000000000 : ℝ)*X 2 1+(-44025141/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4084961377/10000000000 : ℝ)*X 0 0+(5218714483/10000000000 : ℝ)*X 0 1+(628867751/2000000000 : ℝ)*X 0 2+(4084961377/10000000000 : ℝ)*X 1 0+(5218714483/10000000000 : ℝ)*X 1 1+(628867751/2000000000 : ℝ)*X 1 2+(4084961377/10000000000 : ℝ)*X 2 0+(5218714483/10000000000 : ℝ)*X 2 1+(628867751/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43795611390364794428463/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26115803/25000000000000 : ℝ)*(base1) + (104388329/25000000000000 : ℝ)*(base19) + (836148773/100000000000000 : ℝ)*(base23) + (95846589/50000000000000 : ℝ)*(base24) + (64834857/100000000000000 : ℝ)*(upper5) + (209891848944873/25000000000000 : ℝ)*(major0) + (209891848944873/25000000000000 : ℝ)*(major1) + (209891848944873/25000000000000 : ℝ)*(major2) + (1221056175069341/100000000000000 : ℝ)*(sp0) + (122105942192761/10000000000000 : ℝ)*(sp1) + (610529405819487/50000000000000 : ℝ)*(sp2) + (458073370383017/100000000000000 : ℝ)*(sp3) + (3768874797/100000000000000 : ℝ)*(sp4) + (340110881/25000000000000 : ℝ)*(sp7) + (458074835289753/100000000000000 : ℝ)*(f.failure) + (610529919740463/50000000000000 : ℝ)*(f.sum) + (23566164232179/25000000000000000000000000000 : ℝ)*base66 + (102209365032179/50000000000000000000000000000 : ℝ)*base68 + (55244291167821/50000000000000000000000000000 : ℝ)*base69 + (130956349717821/50000000000000000000000000000 : ℝ)*base71 + (81580607257179/25000000000000000000000000000 : ℝ)*base74 + (72216787482179/50000000000000000000000000000 : ℝ)*base76 + (210963219217821/50000000000000000000000000000 : ℝ)*base77 + (263103633767821/50000000000000000000000000000 : ℝ)*base79 + (99855496532179/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (89392617/10000000000000000000000 : ℝ)*base90 + (89392617/10000000000000000000000 : ℝ)*base92 + (89392617/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (470566350795243474613659/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1939957621/100000000000000 : ℝ)*(base19) + (78003297/4000000000000 : ℝ)*(base23) + (98464327/100000000000000 : ℝ)*(base32) + (324769429/100000000000000 : ℝ)*(upper3) + (123329149/50000000000000 : ℝ)*(upper5) + (883550940492263/100000000000000 : ℝ)*(major0) + (883550940492263/100000000000000 : ℝ)*(major1) + (883550940492263/100000000000000 : ℝ)*(major2) + (3217599919/50000000000000 : ℝ)*(sp1) + (833174197/12500000000000 : ℝ)*(sp2) + (321257237596751/25000000000000 : ℝ)*(sp4) + (257004115045909/20000000000000 : ℝ)*(sp5) + (1285020334911003/100000000000000 : ℝ)*(sp6) + (482072518422289/100000000000000 : ℝ)*(sp7) + (96414523377323/20000000000000 : ℝ)*(f.failure) + (321257237596751/25000000000000 : ℝ)*(f.sum) + (117288098115149/100000000000000000000000000000 : ℝ)*base66 + (761705259815149/200000000000000000000000000000 : ℝ)*base68 + (2074347689415149/200000000000000000000000000000 : ℝ)*base70 + (1515625544615149/200000000000000000000000000000 : ℝ)*base72 + (85225083615149/100000000000000000000000000000 : ℝ)*base74 + (1373422498615149/200000000000000000000000000000 : ℝ)*base76 + (755786665615149/200000000000000000000000000000 : ℝ)*base78 + (2177269467215149/200000000000000000000000000000 : ℝ)*base80 + (448159189215149/100000000000000000000000000000 : ℝ)*base82 + (1960347/2000000000000000000000 : ℝ)*base90 + (1960347/2000000000000000000000 : ℝ)*base92 + (1960347/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1674_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5293/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (22859/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1674_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1674_s1_0 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-773895891/5000000000 : ℝ)*x 0 + (2739693183/5000000000 : ℝ)*x 1 + (40246327/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (773895891/5000000000 : ℝ)^5015 ≤ (9589835724421/100000000000000 : ℝ)^3991 := by
    have hnat : (773895891 : ℕ)^5015*100000000000000^3991 ≤ 9589835724421^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773895891 5000000000 9589835724421 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2739693183/5000000000 : ℝ)^5015 ≤ (23478290508747/50000000000000 : ℝ)^3991 := by
    have hnat : (2739693183 : ℕ)^5015*50000000000000^3991 ≤ 23478290508747^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739693183 5000000000 23478290508747 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40246327/78125000 : ℝ)^5015 ≤ (43453583249451/100000000000000 : ℝ)^3991 := by
    have hnat : (40246327 : ℕ)^5015*100000000000000^3991 ≤ 43453583249451^3991*78125000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40246327 78125000 43453583249451 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-773895891/5000000000 : ℝ), (2739693183/5000000000 : ℝ), (40246327/78125000 : ℝ)] ![(9589835724421/100000000000000 : ℝ), (23478290508747/50000000000000 : ℝ), (43453583249451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-773895891/5000000000 : ℝ)|^5015 ≤ (9589835724421/100000000000000 : ℝ)^3991
        have hw : |(-773895891/5000000000 : ℝ)|=(773895891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2739693183/5000000000 : ℝ)|^5015 ≤ (23478290508747/50000000000000 : ℝ)^3991
        have hw : |(2739693183/5000000000 : ℝ)|=(2739693183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40246327/78125000 : ℝ)|^5015 ≤ (43453583249451/100000000000000 : ℝ)^3991
        have hw : |(40246327/78125000 : ℝ)|=(40246327/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s1_1 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677229243/5000000000 : ℝ)*x 0 + (-343548921/2000000000 : ℝ)*x 1 + (2575764817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677229243/5000000000 : ℝ)^5015 ≤ (1425476780461/3125000000000 : ℝ)^3991 := by
    have hnat : (2677229243 : ℕ)^5015*3125000000000^3991 ≤ 1425476780461^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677229243 5000000000 1425476780461 3125000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343548921/2000000000 : ℝ)^5015 ≤ (5465581061487/50000000000000 : ℝ)^3991 := by
    have hnat : (343548921 : ℕ)^5015*50000000000000^3991 ≤ 5465581061487^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343548921 2000000000 5465581061487 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575764817/5000000000 : ℝ)^5015 ≤ (43453580896399/100000000000000 : ℝ)^3991 := by
    have hnat : (2575764817 : ℕ)^5015*100000000000000^3991 ≤ 43453580896399^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575764817 5000000000 43453580896399 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677229243/5000000000 : ℝ), (-343548921/2000000000 : ℝ), (2575764817/5000000000 : ℝ)] ![(1425476780461/3125000000000 : ℝ), (5465581061487/50000000000000 : ℝ), (43453580896399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677229243/5000000000 : ℝ)|^5015 ≤ (1425476780461/3125000000000 : ℝ)^3991
        have hw : |(2677229243/5000000000 : ℝ)|=(2677229243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-343548921/2000000000 : ℝ)|^5015 ≤ (5465581061487/50000000000000 : ℝ)^3991
        have hw : |(-343548921/2000000000 : ℝ)|=(343548921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575764817/5000000000 : ℝ)|^5015 ≤ (43453580896399/100000000000000 : ℝ)^3991
        have hw : |(2575764817/5000000000 : ℝ)|=(2575764817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s1_2 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677228943/5000000000 : ℝ)*x 0 + (5151530369/10000000000 : ℝ)*x 1 + (-1717744433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677228943/5000000000 : ℝ)^5015 ≤ (9123050110359/20000000000000 : ℝ)^3991 := by
    have hnat : (2677228943 : ℕ)^5015*20000000000000^3991 ≤ 9123050110359^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677228943 5000000000 9123050110359 20000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5151530369/10000000000 : ℝ)^5015 ≤ (4345358868691/10000000000000 : ℝ)^3991 := by
    have hnat : (5151530369 : ℕ)^5015*10000000000000^3991 ≤ 4345358868691^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151530369 10000000000 4345358868691 10000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1717744433/10000000000 : ℝ)^5015 ≤ (2186232149517/20000000000000 : ℝ)^3991 := by
    have hnat : (1717744433 : ℕ)^5015*20000000000000^3991 ≤ 2186232149517^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1717744433 10000000000 2186232149517 20000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677228943/5000000000 : ℝ), (5151530369/10000000000 : ℝ), (-1717744433/10000000000 : ℝ)] ![(9123050110359/20000000000000 : ℝ), (4345358868691/10000000000000 : ℝ), (2186232149517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677228943/5000000000 : ℝ)|^5015 ≤ (9123050110359/20000000000000 : ℝ)^3991
        have hw : |(2677228943/5000000000 : ℝ)|=(2677228943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5151530369/10000000000 : ℝ)|^5015 ≤ (4345358868691/10000000000000 : ℝ)^3991
        have hw : |(5151530369/10000000000 : ℝ)|=(5151530369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1717744433/10000000000 : ℝ)|^5015 ≤ (2186232149517/20000000000000 : ℝ)^3991
        have hw : |(-1717744433/10000000000 : ℝ)|=(1717744433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s1_3 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4156955741/10000000000 : ℝ)*x 0 + (1868021487/5000000000 : ℝ)*x 1 + (921997797/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4156955741/10000000000 : ℝ)^5015 ≤ (16593264154759/50000000000000 : ℝ)^3991 := by
    have hnat : (4156955741 : ℕ)^5015*50000000000000^3991 ≤ 16593264154759^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156955741 10000000000 16593264154759 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1868021487/5000000000 : ℝ)^5015 ≤ (29020337164379/100000000000000 : ℝ)^3991 := by
    have hnat : (1868021487 : ℕ)^5015*100000000000000^3991 ≤ 29020337164379^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868021487 5000000000 29020337164379 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (921997797/2000000000 : ℝ)^5015 ≤ (18896567257827/50000000000000 : ℝ)^3991 := by
    have hnat : (921997797 : ℕ)^5015*50000000000000^3991 ≤ 18896567257827^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921997797 2000000000 18896567257827 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4156955741/10000000000 : ℝ), (1868021487/5000000000 : ℝ), (921997797/2000000000 : ℝ)] ![(16593264154759/50000000000000 : ℝ), (29020337164379/100000000000000 : ℝ), (18896567257827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4156955741/10000000000 : ℝ)|^5015 ≤ (16593264154759/50000000000000 : ℝ)^3991
        have hw : |(4156955741/10000000000 : ℝ)|=(4156955741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1868021487/5000000000 : ℝ)|^5015 ≤ (29020337164379/100000000000000 : ℝ)^3991
        have hw : |(1868021487/5000000000 : ℝ)|=(1868021487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(921997797/2000000000 : ℝ)|^5015 ≤ (18896567257827/50000000000000 : ℝ)^3991
        have hw : |(921997797/2000000000 : ℝ)|=(921997797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s1_4 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-77396027/500000000 : ℝ)*x 0 + (5154740909/10000000000 : ℝ)*x 1 + (5476132153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77396027/500000000 : ℝ)^5015 ≤ (4795419091801/50000000000000 : ℝ)^3991 := by
    have hnat : (77396027 : ℕ)^5015*50000000000000^3991 ≤ 4795419091801^3991*500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77396027 500000000 4795419091801 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5154740909/10000000000 : ℝ)^5015 ≤ (21743810497161/50000000000000 : ℝ)^3991 := by
    have hnat : (5154740909 : ℕ)^5015*50000000000000^3991 ≤ 21743810497161^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5154740909 10000000000 21743810497161 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5476132153/10000000000 : ℝ)^5015 ≤ (23460770406467/50000000000000 : ℝ)^3991 := by
    have hnat : (5476132153 : ℕ)^5015*50000000000000^3991 ≤ 23460770406467^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476132153 10000000000 23460770406467 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-77396027/500000000 : ℝ), (5154740909/10000000000 : ℝ), (5476132153/10000000000 : ℝ)] ![(4795419091801/50000000000000 : ℝ), (21743810497161/50000000000000 : ℝ), (23460770406467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-77396027/500000000 : ℝ)|^5015 ≤ (4795419091801/50000000000000 : ℝ)^3991
        have hw : |(-77396027/500000000 : ℝ)|=(77396027/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5154740909/10000000000 : ℝ)|^5015 ≤ (21743810497161/50000000000000 : ℝ)^3991
        have hw : |(5154740909/10000000000 : ℝ)|=(5154740909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5476132153/10000000000 : ℝ)|^5015 ≤ (23460770406467/50000000000000 : ℝ)^3991
        have hw : |(5476132153/10000000000 : ℝ)|=(5476132153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s1_5 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2633304197/5000000000 : ℝ)*x 0 + (-696571279/5000000000 : ℝ)*x 1 + (5476132161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633304197/5000000000 : ℝ)^5015 ≤ (44676815541689/100000000000000 : ℝ)^3991 := by
    have hnat : (2633304197 : ℕ)^5015*100000000000000^3991 ≤ 44676815541689^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633304197 5000000000 44676815541689 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (696571279/5000000000 : ℝ)^5015 ≤ (1050205443687/12500000000000 : ℝ)^3991 := by
    have hnat : (696571279 : ℕ)^5015*12500000000000^3991 ≤ 1050205443687^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696571279 5000000000 1050205443687 12500000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5476132161/10000000000 : ℝ)^5015 ≤ (46921540899069/100000000000000 : ℝ)^3991 := by
    have hnat : (5476132161 : ℕ)^5015*100000000000000^3991 ≤ 46921540899069^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476132161 10000000000 46921540899069 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633304197/5000000000 : ℝ), (-696571279/5000000000 : ℝ), (5476132161/10000000000 : ℝ)] ![(44676815541689/100000000000000 : ℝ), (1050205443687/12500000000000 : ℝ), (46921540899069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633304197/5000000000 : ℝ)|^5015 ≤ (44676815541689/100000000000000 : ℝ)^3991
        have hw : |(2633304197/5000000000 : ℝ)|=(2633304197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-696571279/5000000000 : ℝ)|^5015 ≤ (1050205443687/12500000000000 : ℝ)^3991
        have hw : |(-696571279/5000000000 : ℝ)|=(696571279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5476132161/10000000000 : ℝ)|^5015 ≤ (46921540899069/100000000000000 : ℝ)^3991
        have hw : |(5476132161/10000000000 : ℝ)|=(5476132161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s1_6 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2633304179/5000000000 : ℝ)*x 0 + (5476132123/10000000000 : ℝ)*x 1 + (-696571331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633304179/5000000000 : ℝ)^5015 ≤ (5584601894743/12500000000000 : ℝ)^3991 := by
    have hnat : (2633304179 : ℕ)^5015*12500000000000^3991 ≤ 5584601894743^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633304179 5000000000 5584601894743 12500000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5476132123/10000000000 : ℝ)^5015 ≤ (4692154048993/10000000000000 : ℝ)^3991 := by
    have hnat : (5476132123 : ℕ)^5015*10000000000000^3991 ≤ 4692154048993^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476132123 10000000000 4692154048993 10000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (696571331/5000000000 : ℝ)^5015 ≤ (4200822168807/50000000000000 : ℝ)^3991 := by
    have hnat : (696571331 : ℕ)^5015*50000000000000^3991 ≤ 4200822168807^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696571331 5000000000 4200822168807 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633304179/5000000000 : ℝ), (5476132123/10000000000 : ℝ), (-696571331/5000000000 : ℝ)] ![(5584601894743/12500000000000 : ℝ), (4692154048993/10000000000000 : ℝ), (4200822168807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633304179/5000000000 : ℝ)|^5015 ≤ (5584601894743/12500000000000 : ℝ)^3991
        have hw : |(2633304179/5000000000 : ℝ)|=(2633304179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5476132123/10000000000 : ℝ)|^5015 ≤ (4692154048993/10000000000000 : ℝ)^3991
        have hw : |(5476132123/10000000000 : ℝ)|=(5476132123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-696571331/5000000000 : ℝ)|^5015 ≤ (4200822168807/50000000000000 : ℝ)^3991
        have hw : |(-696571331/5000000000 : ℝ)|=(696571331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s1_7 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4157299597/10000000000 : ℝ)*x 0 + (4601429601/10000000000 : ℝ)*x 1 + (1872359257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4157299597/10000000000 : ℝ)^5015 ≤ (33189977815059/100000000000000 : ℝ)^3991 := by
    have hnat : (4157299597 : ℕ)^5015*100000000000000^3991 ≤ 33189977815059^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4157299597 10000000000 33189977815059 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4601429601/10000000000 : ℝ)^5015 ≤ (37704980674763/100000000000000 : ℝ)^3991 := by
    have hnat : (4601429601 : ℕ)^5015*100000000000000^3991 ≤ 37704980674763^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4601429601 10000000000 37704980674763 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1872359257/5000000000 : ℝ)^5015 ≤ (29105041492173/100000000000000 : ℝ)^3991 := by
    have hnat : (1872359257 : ℕ)^5015*100000000000000^3991 ≤ 29105041492173^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872359257 5000000000 29105041492173 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4157299597/10000000000 : ℝ), (4601429601/10000000000 : ℝ), (1872359257/5000000000 : ℝ)] ![(33189977815059/100000000000000 : ℝ), (37704980674763/100000000000000 : ℝ), (29105041492173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4157299597/10000000000 : ℝ)|^5015 ≤ (33189977815059/100000000000000 : ℝ)^3991
        have hw : |(4157299597/10000000000 : ℝ)|=(4157299597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4601429601/10000000000 : ℝ)|^5015 ≤ (37704980674763/100000000000000 : ℝ)^3991
        have hw : |(4601429601/10000000000 : ℝ)|=(4601429601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1872359257/5000000000 : ℝ)|^5015 ≤ (29105041492173/100000000000000 : ℝ)^3991
        have hw : |(1872359257/5000000000 : ℝ)|=(1872359257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1674_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22859/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10057/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3407/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (22859/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5293/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (22859/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5293/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (22859/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5293/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (22859/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5293/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (22859/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5293/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (22859/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5293/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5293/100000 : ℝ) ^ (5011/1024 : ℝ) ≤ (56802234534721/100000000000000000000 : ℝ) := by
    have hpowers : (5293/100000 : ℝ)^5011 ≤ (56802234534721/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5293 : ℕ)^5011*100000000000000000000^1024 ≤ 56802234534721^1024*100000^5011 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5293 100000 56802234534721 100000000000000000000 5011 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5293/100000 : ℝ)) (X := (56802234534721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (22859/100000 : ℝ) ^ (5011/1024 : ℝ) ≤ (14606342751030817/20000000000000000000 : ℝ) := by
    have hpowers : (22859/100000 : ℝ)^5011 ≤ (14606342751030817/20000000000000000000 : ℝ)^1024 := by
      have hnat : (22859 : ℕ)^5011*20000000000000000000^1024 ≤ 14606342751030817^1024*100000^5011 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22859 100000 14606342751030817 20000000000000000000 5011 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22859/100000 : ℝ)) (X := (14606342751030817/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000056802234534721/50000000000000000000 : ℝ) ≤ (10000002321511151/10000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (50000056802234534721/50000000000000000000 : ℝ)^1024 ≤ (10000002321511151/10000000000000000 : ℝ)^5011 := by
      have hnat : (50000056802234534721 : ℕ)^1024*10000000000000000^5011 ≤ 10000002321511151^5011*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000056802234534721 50000000000000000000 10000002321511151 10000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002321511151/10000000000000000 : ℝ)) (X := (50000056802234534721/50000000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50036544257994844403/50000000000000000000 : ℝ) ≤ (10001493132874193/10000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (50036544257994844403/50000000000000000000 : ℝ)^1024 ≤ (10001493132874193/10000000000000000 : ℝ)^5011 := by
      have hnat : (50036544257994844403 : ℕ)^1024*10000000000000000^5011 ≤ 10001493132874193^5011*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036544257994844403 50000000000000000000 10001493132874193 10000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001493132874193/10000000000000000 : ℝ)) (X := (50036544257994844403/50000000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10014606342751030817/10000000000000000000 : ℝ) ≤ (2000596788847447/2000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (10014606342751030817/10000000000000000000 : ℝ)^1024 ≤ (2000596788847447/2000000000000000 : ℝ)^5011 := by
      have hnat : (10014606342751030817 : ℕ)^1024*2000000000000000^5011 ≤ 2000596788847447^5011*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10014606342751030817 10000000000000000000 2000596788847447 2000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000596788847447/2000000000000000 : ℝ)) (X := (10014606342751030817/10000000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(56802234534721/100000000000000000000 : ℝ) ≤ ((87822129525287857927/87830000000000000000 : ℝ)+2*(745405681521/878300000000000 : ℝ)*(5293/100000 : ℝ))^(5011/1024 : ℝ) := by
    rw [show (87822129525287857927/87830000000000000000 : ℝ)+2*(745405681521/878300000000000 : ℝ)*(5293/100000 : ℝ)=(10000002321511151/10000000000000000 : ℝ) by norm_num, show 1+2*(56802234534721/100000000000000000000 : ℝ)=(50000056802234534721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14606342751030817/20000000000000000000 : ℝ)+(56802234534721/100000000000000000000 : ℝ) ≤ ((87822129525287857927/87830000000000000000 : ℝ)+(745405681521/878300000000000 : ℝ)*((22859/100000 : ℝ)+(5293/100000 : ℝ)))^(5011/1024 : ℝ) := by
    rw [show (87822129525287857927/87830000000000000000 : ℝ)+(745405681521/878300000000000 : ℝ)*((22859/100000 : ℝ)+(5293/100000 : ℝ))=(10001493132874193/10000000000000000 : ℝ) by norm_num, show 1+(14606342751030817/20000000000000000000 : ℝ)+(56802234534721/100000000000000000000 : ℝ)=(50036544257994844403/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14606342751030817/20000000000000000000 : ℝ) ≤ ((87822129525287857927/87830000000000000000 : ℝ)+2*(745405681521/878300000000000 : ℝ)*(22859/100000 : ℝ))^(5011/1024 : ℝ) := by
    rw [show (87822129525287857927/87830000000000000000 : ℝ)+2*(745405681521/878300000000000 : ℝ)*(22859/100000 : ℝ)=(2000596788847447/2000000000000000 : ℝ) by norm_num, show 1+2*(14606342751030817/20000000000000000000 : ℝ)=(10014606342751030817/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (87822129525287857927/87830000000000000000 : ℝ)*(X 1 0+X 2 0)+(745405681521/878300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (5293/100000 : ℝ)) (hi := (22859/100000 : ℝ)) (c := (87822129525287857927/87830000000000000000 : ℝ)) (alpha := (745405681521/878300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (87822129525287857927/87830000000000000000 : ℝ)*(X 0 1+X 2 1)+(745405681521/878300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (5293/100000 : ℝ)) (hi := (22859/100000 : ℝ)) (c := (87822129525287857927/87830000000000000000 : ℝ)) (alpha := (745405681521/878300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (87822129525287857927/87830000000000000000 : ℝ)*(X 0 2+X 1 2)+(745405681521/878300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (5293/100000 : ℝ)) (hi := (22859/100000 : ℝ)) (c := (87822129525287857927/87830000000000000000 : ℝ)) (alpha := (745405681521/878300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-773895891/5000000000 : ℝ)*X 0 0+(2739693183/5000000000 : ℝ)*X 0 1+(40246327/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677229243/5000000000 : ℝ)*X 1 0+(-343548921/2000000000 : ℝ)*X 1 1+(2575764817/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677228943/5000000000 : ℝ)*X 2 0+(5151530369/10000000000 : ℝ)*X 2 1+(-1717744433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4156955741/10000000000 : ℝ)*X 0 0+(1868021487/5000000000 : ℝ)*X 0 1+(921997797/2000000000 : ℝ)*X 0 2+(4156955741/10000000000 : ℝ)*X 1 0+(1868021487/5000000000 : ℝ)*X 1 1+(921997797/2000000000 : ℝ)*X 1 2+(4156955741/10000000000 : ℝ)*X 2 0+(1868021487/5000000000 : ℝ)*X 2 1+(921997797/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-77396027/500000000 : ℝ)*X 0 0+(5154740909/10000000000 : ℝ)*X 0 1+(5476132153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2633304197/5000000000 : ℝ)*X 1 0+(-696571279/5000000000 : ℝ)*X 1 1+(5476132161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2633304179/5000000000 : ℝ)*X 2 0+(5476132123/10000000000 : ℝ)*X 2 1+(-696571331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4157299597/10000000000 : ℝ)*X 0 0+(4601429601/10000000000 : ℝ)*X 0 1+(1872359257/5000000000 : ℝ)*X 0 2+(4157299597/10000000000 : ℝ)*X 1 0+(4601429601/10000000000 : ℝ)*X 1 1+(1872359257/5000000000 : ℝ)*X 1 2+(4157299597/10000000000 : ℝ)*X 2 0+(4601429601/10000000000 : ℝ)*X 2 1+(1872359257/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11005598485670174159352930399/2195750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (426992173/25000000000000 : ℝ)*(base19) + (1217487349/100000000000000 : ℝ)*(base23) + (48289263/20000000000000 : ℝ)*(upper3) + (19904361/25000000000000 : ℝ)*(upper4) + (206169863/100000000000000 : ℝ)*(upper5) + (1048598890531407/50000000000000 : ℝ)*(major0) + (1048598890531407/50000000000000 : ℝ)*(major1) + (1048598890531407/50000000000000 : ℝ)*(major2) + (762532788080033/25000000000000 : ℝ)*(sp0) + (610029086284371/20000000000000 : ℝ)*(sp1) + (1525072960951599/50000000000000 : ℝ)*(sp2) + (572120882387847/50000000000000 : ℝ)*(sp3) + (999191901/6250000000000 : ℝ)*(sp4) + (649088513/10000000000000 : ℝ)*(sp7) + (45769930226433/4000000000000 : ℝ)*(f.failure) + (3050147139390547/100000000000000 : ℝ)*(f.sum) + (89910983490047/21957500000000000000000000000 : ℝ)*base65 + (9836296106059113289/4391500000000000000000000000000000 : ℝ)*base67 + (4621835558177113289/4391500000000000000000000000000000 : ℝ)*base69 + (23943604054001113289/4391500000000000000000000000000000 : ℝ)*base71 + (125160403885029/43915000000000000000000000000 : ℝ)*base73 + (49471327303832113289/4391500000000000000000000000000000 : ℝ)*base75 + (41030456719934113289/4391500000000000000000000000000000 : ℝ)*base77 + (19461359178310113289/4391500000000000000000000000000000 : ℝ)*base79 + (50666811961777/21957500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1666863/400000000000000000000 : ℝ)*base89 + (1666863/400000000000000000000 : ℝ)*base91 + (1666863/400000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9177262000393421869276388487/878300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (861726599/50000000000000 : ℝ)*(base19) + (861491907/50000000000000 : ℝ)*(base23) + (59740243/25000000000000 : ℝ)*(upper3) + (20333393/100000000000000 : ℝ)*(lower4) + (33721913/12500000000000 : ℝ)*(upper5) + (427872736535573/20000000000000 : ℝ)*(major0) + (427872736535573/20000000000000 : ℝ)*(major1) + (427872736535573/20000000000000 : ℝ)*(major2) + (16734178299/100000000000000 : ℝ)*(sp1) + (15666630217/100000000000000 : ℝ)*(sp2) + (311147270073647/10000000000000 : ℝ)*(sp4) + (1555727121552487/50000000000000 : ℝ)*(sp5) + (3111455311122439/100000000000000 : ℝ)*(sp6) + (583627158161423/50000000000000 : ℝ)*(sp7) + (583627158161423/50000000000000 : ℝ)*(f.failure) + (311147270073647/10000000000000 : ℝ)*(f.sum) + (43265330928387/8783000000000000000000000000 : ℝ)*base65 + (15082030720397237171/1756600000000000000000000000000000 : ℝ)*base67 + (2424201101617562829/1756600000000000000000000000000000 : ℝ)*base70 + (213431079012362829/1756600000000000000000000000000000 : ℝ)*base72 + (1806793823323/274468750000000000000000000 : ℝ)*base73 + (365347380180437171/1756600000000000000000000000000000 : ℝ)*base75 + (3209937531751237171/1756600000000000000000000000000000 : ℝ)*base77 + (25928479159253237171/1756600000000000000000000000000000 : ℝ)*base79 + (16406713949481/4391500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (28365247/5000000000000000000000 : ℝ)*base90 + (28365247/5000000000000000000000 : ℝ)*base92 + (28365247/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1674_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22859/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10057/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3407/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1674_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1674_s2_0 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-311012109/2000000000 : ℝ)*x 0 + (2721449889/5000000000 : ℝ)*x 1 + (2591599827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (311012109/2000000000 : ℝ)^5015 ≤ (9646460907217/100000000000000 : ℝ)^3991 := by
    have hnat : (311012109 : ℕ)^5015*100000000000000^3991 ≤ 9646460907217^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311012109 2000000000 9646460907217 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721449889/5000000000 : ℝ)^5015 ≤ (46564012713013/100000000000000 : ℝ)^3991 := by
    have hnat : (2721449889 : ℕ)^5015*100000000000000^3991 ≤ 46564012713013^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721449889 5000000000 46564012713013 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591599827/5000000000 : ℝ)^5015 ≤ (43789526359299/100000000000000 : ℝ)^3991 := by
    have hnat : (2591599827 : ℕ)^5015*100000000000000^3991 ≤ 43789526359299^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591599827 5000000000 43789526359299 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-311012109/2000000000 : ℝ), (2721449889/5000000000 : ℝ), (2591599827/5000000000 : ℝ)] ![(9646460907217/100000000000000 : ℝ), (46564012713013/100000000000000 : ℝ), (43789526359299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-311012109/2000000000 : ℝ)|^5015 ≤ (9646460907217/100000000000000 : ℝ)^3991
        have hw : |(-311012109/2000000000 : ℝ)|=(311012109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721449889/5000000000 : ℝ)|^5015 ≤ (46564012713013/100000000000000 : ℝ)^3991
        have hw : |(2721449889/5000000000 : ℝ)|=(2721449889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591599827/5000000000 : ℝ)|^5015 ≤ (43789526359299/100000000000000 : ℝ)^3991
        have hw : |(2591599827/5000000000 : ℝ)|=(2591599827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s2_1 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66809099/125000000 : ℝ)*x 0 + (-1688693181/10000000000 : ℝ)*x 1 + (518319939/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66809099/125000000 : ℝ)^5015 ≤ (1422222382969/3125000000000 : ℝ)^3991 := by
    have hnat : (66809099 : ℕ)^5015*3125000000000^3991 ≤ 1422222382969^3991*125000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66809099 125000000 1422222382969 3125000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1688693181/10000000000 : ℝ)^5015 ≤ (10699360174223/100000000000000 : ℝ)^3991 := by
    have hnat : (1688693181 : ℕ)^5015*100000000000000^3991 ≤ 10699360174223^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688693181 10000000000 10699360174223 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518319939/1000000000 : ℝ)^5015 ≤ (43789523556671/100000000000000 : ℝ)^3991 := by
    have hnat : (518319939 : ℕ)^5015*100000000000000^3991 ≤ 43789523556671^3991*1000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518319939 1000000000 43789523556671 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66809099/125000000 : ℝ), (-1688693181/10000000000 : ℝ), (518319939/1000000000 : ℝ)] ![(1422222382969/3125000000000 : ℝ), (10699360174223/100000000000000 : ℝ), (43789523556671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66809099/125000000 : ℝ)|^5015 ≤ (1422222382969/3125000000000 : ℝ)^3991
        have hw : |(66809099/125000000 : ℝ)|=(66809099/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1688693181/10000000000 : ℝ)|^5015 ≤ (10699360174223/100000000000000 : ℝ)^3991
        have hw : |(-1688693181/10000000000 : ℝ)|=(1688693181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518319939/1000000000 : ℝ)|^5015 ≤ (43789523556671/100000000000000 : ℝ)^3991
        have hw : |(518319939/1000000000 : ℝ)|=(518319939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s2_2 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672364177/5000000000 : ℝ)*x 0 + (1295799843/2500000000 : ℝ)*x 1 + (-844346311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672364177/5000000000 : ℝ)^5015 ≤ (2275556044939/5000000000000 : ℝ)^3991 := by
    have hnat : (2672364177 : ℕ)^5015*5000000000000^3991 ≤ 2275556044939^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672364177 5000000000 2275556044939 5000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295799843/2500000000 : ℝ)^5015 ≤ (43789523365583/100000000000000 : ℝ)^3991 := by
    have hnat : (1295799843 : ℕ)^5015*100000000000000^3991 ≤ 43789523365583^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295799843 2500000000 43789523365583 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844346311/5000000000 : ℝ)^5015 ≤ (1069935572373/10000000000000 : ℝ)^3991 := by
    have hnat : (844346311 : ℕ)^5015*10000000000000^3991 ≤ 1069935572373^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844346311 5000000000 1069935572373 10000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672364177/5000000000 : ℝ), (1295799843/2500000000 : ℝ), (-844346311/5000000000 : ℝ)] ![(2275556044939/5000000000000 : ℝ), (43789523365583/100000000000000 : ℝ), (1069935572373/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672364177/5000000000 : ℝ)|^5015 ≤ (2275556044939/5000000000000 : ℝ)^3991
        have hw : |(2672364177/5000000000 : ℝ)|=(2672364177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295799843/2500000000 : ℝ)|^5015 ≤ (43789523365583/100000000000000 : ℝ)^3991
        have hw : |(1295799843/2500000000 : ℝ)|=(1295799843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-844346311/5000000000 : ℝ)|^5015 ≤ (1069935572373/10000000000000 : ℝ)^3991
        have hw : |(-844346311/5000000000 : ℝ)|=(844346311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s2_3 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (832480663/2000000000 : ℝ)*x 0 + (1913176311/5000000000 : ℝ)*x 1 + (36148943/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (832480663/2000000000 : ℝ)^5015 ≤ (16620593029967/50000000000000 : ℝ)^3991 := by
    have hnat : (832480663 : ℕ)^5015*50000000000000^3991 ≤ 16620593029967^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832480663 2000000000 16620593029967 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1913176311/5000000000 : ℝ)^5015 ≤ (3738067189031/12500000000000 : ℝ)^3991 := by
    have hnat : (1913176311 : ℕ)^5015*12500000000000^3991 ≤ 3738067189031^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913176311 5000000000 3738067189031 12500000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36148943/80000000 : ℝ)^5015 ≤ (4606784551681/12500000000000 : ℝ)^3991 := by
    have hnat : (36148943 : ℕ)^5015*12500000000000^3991 ≤ 4606784551681^3991*80000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36148943 80000000 4606784551681 12500000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(832480663/2000000000 : ℝ), (1913176311/5000000000 : ℝ), (36148943/80000000 : ℝ)] ![(16620593029967/50000000000000 : ℝ), (3738067189031/12500000000000 : ℝ), (4606784551681/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(832480663/2000000000 : ℝ)|^5015 ≤ (16620593029967/50000000000000 : ℝ)^3991
        have hw : |(832480663/2000000000 : ℝ)|=(832480663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1913176311/5000000000 : ℝ)|^5015 ≤ (3738067189031/12500000000000 : ℝ)^3991
        have hw : |(1913176311/5000000000 : ℝ)|=(1913176311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36148943/80000000 : ℝ)|^5015 ≤ (4606784551681/12500000000000 : ℝ)^3991
        have hw : |(36148943/80000000 : ℝ)|=(36148943/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s2_4 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1555125987/10000000000 : ℝ)*x 0 + (1296304639/2500000000 : ℝ)*x 1 + (5440858393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1555125987/10000000000 : ℝ)^5015 ≤ (4823485511537/50000000000000 : ℝ)^3991 := by
    have hnat : (1555125987 : ℕ)^5015*50000000000000^3991 ≤ 4823485511537^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1555125987 10000000000 4823485511537 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296304639/2500000000 : ℝ)^5015 ≤ (4381096012389/10000000000000 : ℝ)^3991 := by
    have hnat : (1296304639 : ℕ)^5015*10000000000000^3991 ≤ 4381096012389^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296304639 2500000000 4381096012389 10000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440858393/10000000000 : ℝ)^5015 ≤ (1861682753579/4000000000000 : ℝ)^3991 := by
    have hnat : (5440858393 : ℕ)^5015*4000000000000^3991 ≤ 1861682753579^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440858393 10000000000 1861682753579 4000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1555125987/10000000000 : ℝ), (1296304639/2500000000 : ℝ), (5440858393/10000000000 : ℝ)] ![(4823485511537/50000000000000 : ℝ), (4381096012389/10000000000000 : ℝ), (1861682753579/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1555125987/10000000000 : ℝ)|^5015 ≤ (4823485511537/50000000000000 : ℝ)^3991
        have hw : |(-1555125987/10000000000 : ℝ)|=(1555125987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296304639/2500000000 : ℝ)|^5015 ≤ (4381096012389/10000000000000 : ℝ)^3991
        have hw : |(1296304639/2500000000 : ℝ)|=(1296304639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440858393/10000000000 : ℝ)|^5015 ≤ (1861682753579/4000000000000 : ℝ)^3991
        have hw : |(5440858393/10000000000 : ℝ)|=(5440858393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s2_5 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329698461/625000000 : ℝ)*x 0 + (-1431033627/10000000000 : ℝ)*x 1 + (217634323/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329698461/625000000 : ℝ)^5015 ≤ (2798009692743/6250000000000 : ℝ)^3991 := by
    have hnat : (329698461 : ℕ)^5015*6250000000000^3991 ≤ 2798009692743^3991*625000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329698461 625000000 2798009692743 6250000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1431033627/10000000000 : ℝ)^5015 ≤ (8689779479071/100000000000000 : ℝ)^3991 := by
    have hnat : (1431033627 : ℕ)^5015*100000000000000^3991 ≤ 8689779479071^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1431033627 10000000000 8689779479071 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217634323/400000000 : ℝ)^5015 ≤ (23271032710649/50000000000000 : ℝ)^3991 := by
    have hnat : (217634323 : ℕ)^5015*50000000000000^3991 ≤ 23271032710649^3991*400000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217634323 400000000 23271032710649 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329698461/625000000 : ℝ), (-1431033627/10000000000 : ℝ), (217634323/400000000 : ℝ)] ![(2798009692743/6250000000000 : ℝ), (8689779479071/100000000000000 : ℝ), (23271032710649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329698461/625000000 : ℝ)|^5015 ≤ (2798009692743/6250000000000 : ℝ)^3991
        have hw : |(329698461/625000000 : ℝ)|=(329698461/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1431033627/10000000000 : ℝ)|^5015 ≤ (8689779479071/100000000000000 : ℝ)^3991
        have hw : |(-1431033627/10000000000 : ℝ)|=(1431033627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217634323/400000000 : ℝ)|^5015 ≤ (23271032710649/50000000000000 : ℝ)^3991
        have hw : |(217634323/400000000 : ℝ)|=(217634323/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s2_6 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275174271/10000000000 : ℝ)*x 0 + (5440858843/10000000000 : ℝ)*x 1 + (-143103409/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275174271/10000000000 : ℝ)^5015 ≤ (44768143300131/100000000000000 : ℝ)^3991 := by
    have hnat : (5275174271 : ℕ)^5015*100000000000000^3991 ≤ 44768143300131^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275174271 10000000000 44768143300131 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440858843/10000000000 : ℝ)^5015 ≤ (46542073676519/100000000000000 : ℝ)^3991 := by
    have hnat : (5440858843 : ℕ)^5015*100000000000000^3991 ≤ 46542073676519^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440858843 10000000000 46542073676519 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (143103409/1000000000 : ℝ)^5015 ≤ (8689783011953/100000000000000 : ℝ)^3991 := by
    have hnat : (143103409 : ℕ)^5015*100000000000000^3991 ≤ 8689783011953^3991*1000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143103409 1000000000 8689783011953 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275174271/10000000000 : ℝ), (5440858843/10000000000 : ℝ), (-143103409/1000000000 : ℝ)] ![(44768143300131/100000000000000 : ℝ), (46542073676519/100000000000000 : ℝ), (8689783011953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275174271/10000000000 : ℝ)|^5015 ≤ (44768143300131/100000000000000 : ℝ)^3991
        have hw : |(5275174271/10000000000 : ℝ)|=(5275174271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440858843/10000000000 : ℝ)|^5015 ≤ (46542073676519/100000000000000 : ℝ)^3991
        have hw : |(5440858843/10000000000 : ℝ)|=(5440858843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-143103409/1000000000 : ℝ)|^5015 ≤ (8689783011953/100000000000000 : ℝ)^3991
        have hw : |(-143103409/1000000000 : ℝ)|=(143103409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s2_7 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1040643783/2500000000 : ℝ)*x 0 + (1128308541/2500000000 : ℝ)*x 1 + (478974199/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040643783/2500000000 : ℝ)^5015 ≤ (1329716410771/4000000000000 : ℝ)^3991 := by
    have hnat : (1040643783 : ℕ)^5015*4000000000000^3991 ≤ 1329716410771^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040643783 2500000000 1329716410771 4000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128308541/2500000000 : ℝ)^5015 ≤ (36799108467453/100000000000000 : ℝ)^3991 := by
    have hnat : (1128308541 : ℕ)^5015*100000000000000^3991 ≤ 36799108467453^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128308541 2500000000 36799108467453 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478974199/1250000000 : ℝ)^5015 ≤ (14978990625407/50000000000000 : ℝ)^3991 := by
    have hnat : (478974199 : ℕ)^5015*50000000000000^3991 ≤ 14978990625407^3991*1250000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478974199 1250000000 14978990625407 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040643783/2500000000 : ℝ), (1128308541/2500000000 : ℝ), (478974199/1250000000 : ℝ)] ![(1329716410771/4000000000000 : ℝ), (36799108467453/100000000000000 : ℝ), (14978990625407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040643783/2500000000 : ℝ)|^5015 ≤ (1329716410771/4000000000000 : ℝ)^3991
        have hw : |(1040643783/2500000000 : ℝ)|=(1040643783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1128308541/2500000000 : ℝ)|^5015 ≤ (36799108467453/100000000000000 : ℝ)^3991
        have hw : |(1128308541/2500000000 : ℝ)|=(1128308541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(478974199/1250000000 : ℝ)|^5015 ≤ (14978990625407/50000000000000 : ℝ)^3991
        have hw : |(478974199/1250000000 : ℝ)|=(478974199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1674_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3407/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10741/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16271/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3407/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10057/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3407/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10057/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3407/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10057/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3407/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10057/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3407/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10057/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3407/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10057/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10057/100000 : ℝ) ^ (5011/1024 : ℝ) ≤ (1313786540223007/100000000000000000000 : ℝ) := by
    have hpowers : (10057/100000 : ℝ)^5011 ≤ (1313786540223007/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10057 : ℕ)^5011*100000000000000000000^1024 ≤ 1313786540223007^1024*100000^5011 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10057 100000 1313786540223007 100000000000000000000 5011 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10057/100000 : ℝ)) (X := (1313786540223007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3407/20000 : ℝ) ^ (5011/1024 : ℝ) ≤ (17319315187852193/100000000000000000000 : ℝ) := by
    have hpowers : (3407/20000 : ℝ)^5011 ≤ (17319315187852193/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3407 : ℕ)^5011*100000000000000000000^1024 ≤ 17319315187852193^1024*20000^5011 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3407 20000 17319315187852193 100000000000000000000 5011 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3407/20000 : ℝ)) (X := (17319315187852193/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001313786540223007/50000000000000000000 : ℝ) ≤ (10000053694007369/10000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (50001313786540223007/50000000000000000000 : ℝ)^1024 ≤ (10000053694007369/10000000000000000 : ℝ)^5011 := by
      have hnat : (50001313786540223007 : ℕ)^1024*10000000000000000^5011 ≤ 10000053694007369^5011*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001313786540223007 50000000000000000000 10000053694007369 10000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000053694007369/10000000000000000 : ℝ)) (X := (50001313786540223007/50000000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (62511645688580047/62500000000000000 : ℝ) ≤ (5000190370005591/5000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (62511645688580047/62500000000000000 : ℝ)^1024 ≤ (5000190370005591/5000000000000000 : ℝ)^5011 := by
      have hnat : (62511645688580047 : ℕ)^1024*5000000000000000^5011 ≤ 5000190370005591^5011*62500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62511645688580047 62500000000000000 5000190370005591 5000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000190370005591/5000000000000000 : ℝ)) (X := (62511645688580047/62500000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50017319315187852193/50000000000000000000 : ℝ) ≤ (2000141557202999/2000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (50017319315187852193/50000000000000000000 : ℝ)^1024 ≤ (2000141557202999/2000000000000000 : ℝ)^5011 := by
      have hnat : (50017319315187852193 : ℕ)^1024*2000000000000000^5011 ≤ 2000141557202999^5011*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017319315187852193 50000000000000000000 2000141557202999 2000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000141557202999/2000000000000000 : ℝ)) (X := (50017319315187852193/50000000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1313786540223007/100000000000000000000 : ℝ) ≤ ((348868982367313631/348900000000000000 : ℝ)+2*(327046003813/697800000000000 : ℝ)*(10057/100000 : ℝ))^(5011/1024 : ℝ) := by
    rw [show (348868982367313631/348900000000000000 : ℝ)+2*(327046003813/697800000000000 : ℝ)*(10057/100000 : ℝ)=(10000053694007369/10000000000000000 : ℝ) by norm_num, show 1+2*(1313786540223007/100000000000000000000 : ℝ)=(50001313786540223007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17319315187852193/100000000000000000000 : ℝ)+(1313786540223007/100000000000000000000 : ℝ) ≤ ((348868982367313631/348900000000000000 : ℝ)+(327046003813/697800000000000 : ℝ)*((3407/20000 : ℝ)+(10057/100000 : ℝ)))^(5011/1024 : ℝ) := by
    rw [show (348868982367313631/348900000000000000 : ℝ)+(327046003813/697800000000000 : ℝ)*((3407/20000 : ℝ)+(10057/100000 : ℝ))=(5000190370005591/5000000000000000 : ℝ) by norm_num, show 1+(17319315187852193/100000000000000000000 : ℝ)+(1313786540223007/100000000000000000000 : ℝ)=(62511645688580047/62500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17319315187852193/100000000000000000000 : ℝ) ≤ ((348868982367313631/348900000000000000 : ℝ)+2*(327046003813/697800000000000 : ℝ)*(3407/20000 : ℝ))^(5011/1024 : ℝ) := by
    rw [show (348868982367313631/348900000000000000 : ℝ)+2*(327046003813/697800000000000 : ℝ)*(3407/20000 : ℝ)=(2000141557202999/2000000000000000 : ℝ) by norm_num, show 1+2*(17319315187852193/100000000000000000000 : ℝ)=(50017319315187852193/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (348868982367313631/348900000000000000 : ℝ)*(X 1 0+X 2 0)+(327046003813/697800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (10057/100000 : ℝ)) (hi := (3407/20000 : ℝ)) (c := (348868982367313631/348900000000000000 : ℝ)) (alpha := (327046003813/697800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (348868982367313631/348900000000000000 : ℝ)*(X 0 1+X 2 1)+(327046003813/697800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (10057/100000 : ℝ)) (hi := (3407/20000 : ℝ)) (c := (348868982367313631/348900000000000000 : ℝ)) (alpha := (327046003813/697800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (348868982367313631/348900000000000000 : ℝ)*(X 0 2+X 1 2)+(327046003813/697800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (10057/100000 : ℝ)) (hi := (3407/20000 : ℝ)) (c := (348868982367313631/348900000000000000 : ℝ)) (alpha := (327046003813/697800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-311012109/2000000000 : ℝ)*X 0 0+(2721449889/5000000000 : ℝ)*X 0 1+(2591599827/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66809099/125000000 : ℝ)*X 1 0+(-1688693181/10000000000 : ℝ)*X 1 1+(518319939/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672364177/5000000000 : ℝ)*X 2 0+(1295799843/2500000000 : ℝ)*X 2 1+(-844346311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((832480663/2000000000 : ℝ)*X 0 0+(1913176311/5000000000 : ℝ)*X 0 1+(36148943/80000000 : ℝ)*X 0 2+(832480663/2000000000 : ℝ)*X 1 0+(1913176311/5000000000 : ℝ)*X 1 1+(36148943/80000000 : ℝ)*X 1 2+(832480663/2000000000 : ℝ)*X 2 0+(1913176311/5000000000 : ℝ)*X 2 1+(36148943/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1555125987/10000000000 : ℝ)*X 0 0+(1296304639/2500000000 : ℝ)*X 0 1+(5440858393/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((329698461/625000000 : ℝ)*X 1 0+(-1431033627/10000000000 : ℝ)*X 1 1+(217634323/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5275174271/10000000000 : ℝ)*X 2 0+(5440858843/10000000000 : ℝ)*X 2 1+(-143103409/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1040643783/2500000000 : ℝ)*X 0 0+(1128308541/2500000000 : ℝ)*X 0 1+(478974199/1250000000 : ℝ)*X 0 2+(1040643783/2500000000 : ℝ)*X 1 0+(1128308541/2500000000 : ℝ)*X 1 1+(478974199/1250000000 : ℝ)*X 1 2+(1040643783/2500000000 : ℝ)*X 2 0+(1128308541/2500000000 : ℝ)*X 2 1+(478974199/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2774066998680138273056421/290750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (575235557/50000000000000 : ℝ)*(base19) + (1254432073/100000000000000 : ℝ)*(base23) + (65146761/50000000000000 : ℝ)*(lower2) + (181044723/100000000000000 : ℝ)*(upper5) + (264758607076091/10000000000000 : ℝ)*(major0) + (264758607076091/10000000000000 : ℝ)*(major1) + (264758607076091/10000000000000 : ℝ)*(major2) + (3850606960546191/100000000000000 : ℝ)*(sp0) + (48132792151979/1250000000000 : ℝ)*(sp1) + (481328245332239/12500000000000 : ℝ)*(sp2) + (722269442041823/50000000000000 : ℝ)*(sp3) + (10128271897/50000000000000 : ℝ)*(sp4) + (336807569/12500000000000 : ℝ)*(sp5) + (1430578103/25000000000000 : ℝ)*(sp7) + (722272303198029/50000000000000 : ℝ)*(f.failure) + (770125443417997/20000000000000 : ℝ)*(f.sum) + (8462687329297/1744500000000000000000000000 : ℝ)*base65 + (27733571646150079/3489000000000000000000000000000 : ℝ)*base68 + (5894408750802079/3489000000000000000000000000000 : ℝ)*base70 + (27347466289926079/3489000000000000000000000000000 : ℝ)*base72 + (7718080707899/3489000000000000000000000000 : ℝ)*base73 + (60763822691118079/3489000000000000000000000000000 : ℝ)*base76 + (13157120097929921/3489000000000000000000000000000 : ℝ)*base77 + (49020463766928079/3489000000000000000000000000000 : ℝ)*base80 + (2555089760227/3489000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (26947619/5000000000000000000000 : ℝ)*base89 + (26947619/5000000000000000000000 : ℝ)*base91 + (26947619/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28944017766083443879353449/2907500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2540013507/100000000000000 : ℝ)*(base19) + (262191989/12500000000000 : ℝ)*(base23) + (251810463/100000000000000 : ℝ)*(upper2) + (244896977/100000000000000 : ℝ)*(upper3) + (245328889/50000000000000 : ℝ)*(upper5) + (1344806721379393/50000000000000 : ℝ)*(major0) + (1344806721379393/50000000000000 : ℝ)*(major1) + (1344806721379393/50000000000000 : ℝ)*(major2) + (30611719277/100000000000000 : ℝ)*(sp1) + (5748600227/25000000000000 : ℝ)*(sp2) + (977937867379883/25000000000000 : ℝ)*(sp4) + (977929579446687/25000000000000 : ℝ)*(sp5) + (3911726377582711/100000000000000 : ℝ)*(sp6) + (366868771041589/25000000000000 : ℝ)*(sp7) + (366868771041589/25000000000000 : ℝ)*(f.failure) + (977937867379883/25000000000000 : ℝ)*(f.sum) + (102217402314551/17445000000000000000000000000 : ℝ)*base66 + (216730324876159517/17445000000000000000000000000000 : ℝ)*base68 + (270286486250299517/17445000000000000000000000000000 : ℝ)*base70 + (220918309461439517/17445000000000000000000000000000 : ℝ)*base72 + (9066951949093/8722500000000000000000000000 : ℝ)*base74 + (235776770747329517/17445000000000000000000000000000 : ℝ)*base76 + (214284726532564517/17445000000000000000000000000000 : ℝ)*base78 + (46454169469024517/17445000000000000000000000000000 : ℝ)*base80 + (4579298829739/17445000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (34078779/2500000000000000000000 : ℝ)*base89 + (34078779/2500000000000000000000 : ℝ)*base91 + (34078779/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1674_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3407/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10741/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1674_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1674_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10741/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1674_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1674_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1674_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10741/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1674_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
