-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1597_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:38:24.033365+00:00
-- url     : https://prove2.me/submissions/06e29cff-931f-4f42-8d9a-82a146437c09

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
theorem support_rectangle_w1597_box_0 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-291772289/2000000000 : ℝ)*x 0 + (5421442521/10000000000 : ℝ)*x 1 + (1084288417/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (291772289/2000000000 : ℝ)^4707 ≤ (4271214243119/50000000000000 : ℝ)^3683 := by
    have hnat : (291772289 : ℕ)^4707*50000000000000^3683 ≤ 4271214243119^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291772289 2000000000 4271214243119 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421442521/10000000000 : ℝ)^4707 ≤ (22864394047113/50000000000000 : ℝ)^3683 := by
    have hnat : (5421442521 : ℕ)^4707*50000000000000^3683 ≤ 22864394047113^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421442521 10000000000 22864394047113 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084288417/2000000000 : ℝ)^4707 ≤ (22864391697081/50000000000000 : ℝ)^3683 := by
    have hnat : (1084288417 : ℕ)^4707*50000000000000^3683 ≤ 22864391697081^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084288417 2000000000 22864391697081 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-291772289/2000000000 : ℝ), (5421442521/10000000000 : ℝ), (1084288417/2000000000 : ℝ)] ![(4271214243119/50000000000000 : ℝ), (22864394047113/50000000000000 : ℝ), (22864391697081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-291772289/2000000000 : ℝ)|^4707 ≤ (4271214243119/50000000000000 : ℝ)^3683
        have hw : |(-291772289/2000000000 : ℝ)|=(291772289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421442521/10000000000 : ℝ)|^4707 ≤ (22864394047113/50000000000000 : ℝ)^3683
        have hw : |(5421442521/10000000000 : ℝ)|=(5421442521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084288417/2000000000 : ℝ)|^4707 ≤ (22864391697081/50000000000000 : ℝ)^3683
        have hw : |(1084288417/2000000000 : ℝ)|=(1084288417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_1 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656368061/1250000000 : ℝ)*x 0 + (-849062343/5000000000 : ℝ)*x 1 + (5421442191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656368061/1250000000 : ℝ)^4707 ≤ (4389892251173/10000000000000 : ℝ)^3683 := by
    have hnat : (656368061 : ℕ)^4707*10000000000000^3683 ≤ 4389892251173^3683*1250000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656368061 1250000000 4389892251173 10000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849062343/5000000000 : ℝ)^4707 ≤ (10372292937211/100000000000000 : ℝ)^3683 := by
    have hnat : (849062343 : ℕ)^4707*100000000000000^3683 ≤ 10372292937211^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849062343 5000000000 10372292937211 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421442191/10000000000 : ℝ)^4707 ≤ (22864392268419/50000000000000 : ℝ)^3683 := by
    have hnat : (5421442191 : ℕ)^4707*50000000000000^3683 ≤ 22864392268419^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421442191 10000000000 22864392268419 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656368061/1250000000 : ℝ), (-849062343/5000000000 : ℝ), (5421442191/10000000000 : ℝ)] ![(4389892251173/10000000000000 : ℝ), (10372292937211/100000000000000 : ℝ), (22864392268419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656368061/1250000000 : ℝ)|^4707 ≤ (4389892251173/10000000000000 : ℝ)^3683
        have hw : |(656368061/1250000000 : ℝ)|=(656368061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-849062343/5000000000 : ℝ)|^4707 ≤ (10372292937211/100000000000000 : ℝ)^3683
        have hw : |(-849062343/5000000000 : ℝ)|=(849062343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421442191/10000000000 : ℝ)|^4707 ≤ (22864392268419/50000000000000 : ℝ)^3683
        have hw : |(5421442191/10000000000 : ℝ)|=(5421442191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_2 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250944183/10000000000 : ℝ)*x 0 + (2710721149/5000000000 : ℝ)*x 1 + (-339624991/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250944183/10000000000 : ℝ)^4707 ≤ (21949459626461/50000000000000 : ℝ)^3683 := by
    have hnat : (5250944183 : ℕ)^4707*50000000000000^3683 ≤ 21949459626461^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250944183 10000000000 21949459626461 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710721149/5000000000 : ℝ)^4707 ≤ (22864392845147/50000000000000 : ℝ)^3683 := by
    have hnat : (2710721149 : ℕ)^4707*50000000000000^3683 ≤ 22864392845147^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710721149 5000000000 22864392845147 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339624991/2000000000 : ℝ)^4707 ≤ (5186147518559/50000000000000 : ℝ)^3683 := by
    have hnat : (339624991 : ℕ)^4707*50000000000000^3683 ≤ 5186147518559^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339624991 2000000000 5186147518559 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250944183/10000000000 : ℝ), (2710721149/5000000000 : ℝ), (-339624991/2000000000 : ℝ)] ![(21949459626461/50000000000000 : ℝ), (22864392845147/50000000000000 : ℝ), (5186147518559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250944183/10000000000 : ℝ)|^4707 ≤ (21949459626461/50000000000000 : ℝ)^3683
        have hw : |(5250944183/10000000000 : ℝ)|=(5250944183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710721149/5000000000 : ℝ)|^4707 ≤ (22864392845147/50000000000000 : ℝ)^3683
        have hw : |(2710721149/5000000000 : ℝ)|=(2710721149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-339624991/2000000000 : ℝ)|^4707 ≤ (5186147518559/50000000000000 : ℝ)^3683
        have hw : |(-339624991/2000000000 : ℝ)|=(339624991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_3 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (900887453/2000000000 : ℝ)*x 0 + (819173661/2000000000 : ℝ)*x 1 + (819173533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (900887453/2000000000 : ℝ)^4707 ≤ (36086167795777/100000000000000 : ℝ)^3683 := by
    have hnat : (900887453 : ℕ)^4707*100000000000000^3683 ≤ 36086167795777^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900887453 2000000000 36086167795777 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (819173661/2000000000 : ℝ)^4707 ≤ (6391383857241/20000000000000 : ℝ)^3683 := by
    have hnat : (819173661 : ℕ)^4707*20000000000000^3683 ≤ 6391383857241^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819173661 2000000000 6391383857241 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (819173533/2000000000 : ℝ)^4707 ≤ (1997307056527/6250000000000 : ℝ)^3683 := by
    have hnat : (819173533 : ℕ)^4707*6250000000000^3683 ≤ 1997307056527^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819173533 2000000000 1997307056527 6250000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(900887453/2000000000 : ℝ), (819173661/2000000000 : ℝ), (819173533/2000000000 : ℝ)] ![(36086167795777/100000000000000 : ℝ), (6391383857241/20000000000000 : ℝ), (1997307056527/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(900887453/2000000000 : ℝ)|^4707 ≤ (36086167795777/100000000000000 : ℝ)^3683
        have hw : |(900887453/2000000000 : ℝ)|=(900887453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(819173661/2000000000 : ℝ)|^4707 ≤ (6391383857241/20000000000000 : ℝ)^3683
        have hw : |(819173661/2000000000 : ℝ)|=(819173661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(819173533/2000000000 : ℝ)|^4707 ≤ (1997307056527/6250000000000 : ℝ)^3683
        have hw : |(819173533/2000000000 : ℝ)|=(819173533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_4 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1013529957/5000000000 : ℝ)*x 0 + (5213278431/10000000000 : ℝ)*x 1 + (1042655781/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013529957/5000000000 : ℝ)^4707 ≤ (13006240583969/100000000000000 : ℝ)^3683 := by
    have hnat : (1013529957 : ℕ)^4707*100000000000000^3683 ≤ 13006240583969^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013529957 5000000000 13006240583969 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213278431/10000000000 : ℝ)^4707 ≤ (43496877175597/100000000000000 : ℝ)^3683 := by
    have hnat : (5213278431 : ℕ)^4707*100000000000000^3683 ≤ 43496877175597^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213278431 10000000000 43496877175597 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042655781/2000000000 : ℝ)^4707 ≤ (21748441114989/50000000000000 : ℝ)^3683 := by
    have hnat : (1042655781 : ℕ)^4707*50000000000000^3683 ≤ 21748441114989^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042655781 2000000000 21748441114989 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1013529957/5000000000 : ℝ), (5213278431/10000000000 : ℝ), (1042655781/2000000000 : ℝ)] ![(13006240583969/100000000000000 : ℝ), (43496877175597/100000000000000 : ℝ), (21748441114989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1013529957/5000000000 : ℝ)|^4707 ≤ (13006240583969/100000000000000 : ℝ)^3683
        have hw : |(-1013529957/5000000000 : ℝ)|=(1013529957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213278431/10000000000 : ℝ)|^4707 ≤ (43496877175597/100000000000000 : ℝ)^3683
        have hw : |(5213278431/10000000000 : ℝ)|=(5213278431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042655781/2000000000 : ℝ)|^4707 ≤ (21748441114989/50000000000000 : ℝ)^3683
        have hw : |(1042655781/2000000000 : ℝ)|=(1042655781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_5 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394880319/10000000000 : ℝ)*x 0 + (-892830661/5000000000 : ℝ)*x 1 + (1042655827/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394880319/10000000000 : ℝ)^4707 ≤ (45442643770141/100000000000000 : ℝ)^3683 := by
    have hnat : (5394880319 : ℕ)^4707*100000000000000^3683 ≤ 45442643770141^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394880319 10000000000 45442643770141 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (892830661/5000000000 : ℝ)^4707 ≤ (5530235767451/50000000000000 : ℝ)^3683 := by
    have hnat : (892830661 : ℕ)^4707*50000000000000^3683 ≤ 5530235767451^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892830661 5000000000 5530235767451 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042655827/2000000000 : ℝ)^4707 ≤ (21748442341263/50000000000000 : ℝ)^3683 := by
    have hnat : (1042655827 : ℕ)^4707*50000000000000^3683 ≤ 21748442341263^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042655827 2000000000 21748442341263 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394880319/10000000000 : ℝ), (-892830661/5000000000 : ℝ), (1042655827/2000000000 : ℝ)] ![(45442643770141/100000000000000 : ℝ), (5530235767451/50000000000000 : ℝ), (21748442341263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394880319/10000000000 : ℝ)|^4707 ≤ (45442643770141/100000000000000 : ℝ)^3683
        have hw : |(5394880319/10000000000 : ℝ)|=(5394880319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-892830661/5000000000 : ℝ)|^4707 ≤ (5530235767451/50000000000000 : ℝ)^3683
        have hw : |(-892830661/5000000000 : ℝ)|=(892830661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042655827/2000000000 : ℝ)|^4707 ≤ (21748442341263/50000000000000 : ℝ)^3683
        have hw : |(1042655827/2000000000 : ℝ)|=(1042655827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_6 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394881607/10000000000 : ℝ)*x 0 + (5213277643/10000000000 : ℝ)*x 1 + (-1785661581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394881607/10000000000 : ℝ)^4707 ≤ (11360664408947/25000000000000 : ℝ)^3683 := by
    have hnat : (5394881607 : ℕ)^4707*25000000000000^3683 ≤ 11360664408947^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394881607 10000000000 11360664408947 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213277643/10000000000 : ℝ)^4707 ≤ (8699373754591/20000000000000 : ℝ)^3683 := by
    have hnat : (5213277643 : ℕ)^4707*20000000000000^3683 ≤ 8699373754591^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213277643 10000000000 8699373754591 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1785661581/10000000000 : ℝ)^4707 ≤ (11060473585199/100000000000000 : ℝ)^3683 := by
    have hnat : (1785661581 : ℕ)^4707*100000000000000^3683 ≤ 11060473585199^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1785661581 10000000000 11060473585199 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394881607/10000000000 : ℝ), (5213277643/10000000000 : ℝ), (-1785661581/10000000000 : ℝ)] ![(11360664408947/25000000000000 : ℝ), (8699373754591/20000000000000 : ℝ), (11060473585199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394881607/10000000000 : ℝ)|^4707 ≤ (11360664408947/25000000000000 : ℝ)^3683
        have hw : |(5394881607/10000000000 : ℝ)|=(5394881607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213277643/10000000000 : ℝ)|^4707 ≤ (8699373754591/20000000000000 : ℝ)^3683
        have hw : |(5213277643/10000000000 : ℝ)|=(5213277643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1785661581/10000000000 : ℝ)|^4707 ≤ (11060473585199/100000000000000 : ℝ)^3683
        have hw : |(-1785661581/10000000000 : ℝ)|=(1785661581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_7 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (787340887/2000000000 : ℝ)*x 0 + (27371147/62500000 : ℝ)*x 1 + (4379384381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (787340887/2000000000 : ℝ)^4707 ≤ (30378468777069/100000000000000 : ℝ)^3683 := by
    have hnat : (787340887 : ℕ)^4707*100000000000000^3683 ≤ 30378468777069^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787340887 2000000000 30378468777069 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27371147/62500000 : ℝ)^4707 ≤ (4351345153943/12500000000000 : ℝ)^3683 := by
    have hnat : (27371147 : ℕ)^4707*12500000000000^3683 ≤ 4351345153943^3683*62500000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27371147 62500000 4351345153943 12500000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4379384381/10000000000 : ℝ)^4707 ≤ (8702692494571/25000000000000 : ℝ)^3683 := by
    have hnat : (4379384381 : ℕ)^4707*25000000000000^3683 ≤ 8702692494571^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379384381 10000000000 8702692494571 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(787340887/2000000000 : ℝ), (27371147/62500000 : ℝ), (4379384381/10000000000 : ℝ)] ![(30378468777069/100000000000000 : ℝ), (4351345153943/12500000000000 : ℝ), (8702692494571/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(787340887/2000000000 : ℝ)|^4707 ≤ (30378468777069/100000000000000 : ℝ)^3683
        have hw : |(787340887/2000000000 : ℝ)|=(787340887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27371147/62500000 : ℝ)|^4707 ≤ (4351345153943/12500000000000 : ℝ)^3683
        have hw : |(27371147/62500000 : ℝ)|=(27371147/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4379384381/10000000000 : ℝ)|^4707 ≤ (8702692494571/25000000000000 : ℝ)^3683
        have hw : |(4379384381/10000000000 : ℝ)|=(4379384381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_8 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1906410773/10000000000 : ℝ)*x 0 + (5064928797/10000000000 : ℝ)*x 1 + (5451542829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1906410773/10000000000 : ℝ)^4707 ≤ (6012596304419/50000000000000 : ℝ)^3683 := by
    have hnat : (1906410773 : ℕ)^4707*50000000000000^3683 ≤ 6012596304419^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906410773 10000000000 6012596304419 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5064928797/10000000000 : ℝ)^4707 ≤ (8384257787049/20000000000000 : ℝ)^3683 := by
    have hnat : (5064928797 : ℕ)^4707*20000000000000^3683 ≤ 8384257787049^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5064928797 10000000000 8384257787049 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451542829/10000000000 : ℝ)^4707 ≤ (46053518444469/100000000000000 : ℝ)^3683 := by
    have hnat : (5451542829 : ℕ)^4707*100000000000000^3683 ≤ 46053518444469^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451542829 10000000000 46053518444469 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1906410773/10000000000 : ℝ), (5064928797/10000000000 : ℝ), (5451542829/10000000000 : ℝ)] ![(6012596304419/50000000000000 : ℝ), (8384257787049/20000000000000 : ℝ), (46053518444469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1906410773/10000000000 : ℝ)|^4707 ≤ (6012596304419/50000000000000 : ℝ)^3683
        have hw : |(-1906410773/10000000000 : ℝ)|=(1906410773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5064928797/10000000000 : ℝ)|^4707 ≤ (8384257787049/20000000000000 : ℝ)^3683
        have hw : |(5064928797/10000000000 : ℝ)|=(5064928797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451542829/10000000000 : ℝ)|^4707 ≤ (46053518444469/100000000000000 : ℝ)^3683
        have hw : |(5451542829/10000000000 : ℝ)|=(5451542829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_9 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615062137/5000000000 : ℝ)*x 0 + (-336998619/2000000000 : ℝ)*x 1 + (340721419/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615062137/5000000000 : ℝ)^4707 ≤ (21838294629841/50000000000000 : ℝ)^3683 := by
    have hnat : (2615062137 : ℕ)^4707*50000000000000^3683 ≤ 21838294629841^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615062137 5000000000 21838294629841 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336998619/2000000000 : ℝ)^4707 ≤ (1026989362801/10000000000000 : ℝ)^3683 := by
    have hnat : (336998619 : ℕ)^4707*10000000000000^3683 ≤ 1026989362801^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336998619 2000000000 1026989362801 10000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340721419/625000000 : ℝ)^4707 ≤ (46053517094897/100000000000000 : ℝ)^3683 := by
    have hnat : (340721419 : ℕ)^4707*100000000000000^3683 ≤ 46053517094897^3683*625000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340721419 625000000 46053517094897 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615062137/5000000000 : ℝ), (-336998619/2000000000 : ℝ), (340721419/625000000 : ℝ)] ![(21838294629841/50000000000000 : ℝ), (1026989362801/10000000000000 : ℝ), (46053517094897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615062137/5000000000 : ℝ)|^4707 ≤ (21838294629841/50000000000000 : ℝ)^3683
        have hw : |(2615062137/5000000000 : ℝ)|=(2615062137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-336998619/2000000000 : ℝ)|^4707 ≤ (1026989362801/10000000000000 : ℝ)^3683
        have hw : |(-336998619/2000000000 : ℝ)|=(336998619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340721419/625000000 : ℝ)|^4707 ≤ (46053517094897/100000000000000 : ℝ)^3683
        have hw : |(340721419/625000000 : ℝ)|=(340721419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_10 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615062381/5000000000 : ℝ)*x 0 + (5451542947/10000000000 : ℝ)*x 1 + (-168499209/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615062381/5000000000 : ℝ)^4707 ≤ (43676594468019/100000000000000 : ℝ)^3683 := by
    have hnat : (2615062381 : ℕ)^4707*100000000000000^3683 ≤ 43676594468019^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615062381 5000000000 43676594468019 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451542947/10000000000 : ℝ)^4707 ≤ (719586245601/1562500000000 : ℝ)^3683 := by
    have hnat : (5451542947 : ℕ)^4707*1562500000000^3683 ≤ 719586245601^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451542947 10000000000 719586245601 1562500000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168499209/1000000000 : ℝ)^4707 ≤ (205397715991/2000000000000 : ℝ)^3683 := by
    have hnat : (168499209 : ℕ)^4707*2000000000000^3683 ≤ 205397715991^3683*1000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168499209 1000000000 205397715991 2000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615062381/5000000000 : ℝ), (5451542947/10000000000 : ℝ), (-168499209/1000000000 : ℝ)] ![(43676594468019/100000000000000 : ℝ), (719586245601/1562500000000 : ℝ), (205397715991/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615062381/5000000000 : ℝ)|^4707 ≤ (43676594468019/100000000000000 : ℝ)^3683
        have hw : |(2615062381/5000000000 : ℝ)|=(2615062381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451542947/10000000000 : ℝ)|^4707 ≤ (719586245601/1562500000000 : ℝ)^3683
        have hw : |(5451542947/10000000000 : ℝ)|=(5451542947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-168499209/1000000000 : ℝ)|^4707 ≤ (205397715991/2000000000000 : ℝ)^3683
        have hw : |(-168499209/1000000000 : ℝ)|=(168499209/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_11 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4584127529/10000000000 : ℝ)*x 0 + (4054798183/10000000000 : ℝ)*x 1 + (4054797513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4584127529/10000000000 : ℝ)^4707 ≤ (288313177641/781250000000 : ℝ)^3683 := by
    have hnat : (4584127529 : ℕ)^4707*781250000000^3683 ≤ 288313177641^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4584127529 10000000000 288313177641 781250000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4054798183/10000000000 : ℝ)^4707 ≤ (15773979980263/50000000000000 : ℝ)^3683 := by
    have hnat : (4054798183 : ℕ)^4707*50000000000000^3683 ≤ 15773979980263^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4054798183 10000000000 15773979980263 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4054797513/10000000000 : ℝ)^4707 ≤ (31547953298301/100000000000000 : ℝ)^3683 := by
    have hnat : (4054797513 : ℕ)^4707*100000000000000^3683 ≤ 31547953298301^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4054797513 10000000000 31547953298301 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4584127529/10000000000 : ℝ), (4054798183/10000000000 : ℝ), (4054797513/10000000000 : ℝ)] ![(288313177641/781250000000 : ℝ), (15773979980263/50000000000000 : ℝ), (31547953298301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4584127529/10000000000 : ℝ)|^4707 ≤ (288313177641/781250000000 : ℝ)^3683
        have hw : |(4584127529/10000000000 : ℝ)|=(4584127529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4054798183/10000000000 : ℝ)|^4707 ≤ (15773979980263/50000000000000 : ℝ)^3683
        have hw : |(4054798183/10000000000 : ℝ)|=(4054798183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4054797513/10000000000 : ℝ)|^4707 ≤ (31547953298301/100000000000000 : ℝ)^3683
        have hw : |(4054797513/10000000000 : ℝ)|=(4054797513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_12 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1578493657/10000000000 : ℝ)*x 0 + (5563633563/10000000000 : ℝ)*x 1 + (2596704917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1578493657/10000000000 : ℝ)^4707 ≤ (2361929500043/25000000000000 : ℝ)^3683 := by
    have hnat : (1578493657 : ℕ)^4707*25000000000000^3683 ≤ 2361929500043^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1578493657 10000000000 2361929500043 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5563633563/10000000000 : ℝ)^4707 ≤ (47267156292989/100000000000000 : ℝ)^3683 := by
    have hnat : (5563633563 : ℕ)^4707*100000000000000^3683 ≤ 47267156292989^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5563633563 10000000000 47267156292989 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2596704917/5000000000 : ℝ)^4707 ≤ (21642562844023/50000000000000 : ℝ)^3683 := by
    have hnat : (2596704917 : ℕ)^4707*50000000000000^3683 ≤ 21642562844023^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596704917 5000000000 21642562844023 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1578493657/10000000000 : ℝ), (5563633563/10000000000 : ℝ), (2596704917/5000000000 : ℝ)] ![(2361929500043/25000000000000 : ℝ), (47267156292989/100000000000000 : ℝ), (21642562844023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1578493657/10000000000 : ℝ)|^4707 ≤ (2361929500043/25000000000000 : ℝ)^3683
        have hw : |(-1578493657/10000000000 : ℝ)|=(1578493657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5563633563/10000000000 : ℝ)|^4707 ≤ (47267156292989/100000000000000 : ℝ)^3683
        have hw : |(5563633563/10000000000 : ℝ)|=(5563633563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2596704917/5000000000 : ℝ)|^4707 ≤ (21642562844023/50000000000000 : ℝ)^3683
        have hw : |(2596704917/5000000000 : ℝ)|=(2596704917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_13 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081725079/2000000000 : ℝ)*x 0 + (-1793708957/10000000000 : ℝ)*x 1 + (519340897/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081725079/2000000000 : ℝ)^4707 ≤ (356177073221/781250000000 : ℝ)^3683 := by
    have hnat : (1081725079 : ℕ)^4707*781250000000^3683 ≤ 356177073221^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081725079 2000000000 356177073221 781250000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1793708957/10000000000 : ℝ)^4707 ≤ (5562109066783/50000000000000 : ℝ)^3683 := by
    have hnat : (1793708957 : ℕ)^4707*50000000000000^3683 ≤ 5562109066783^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793708957 10000000000 5562109066783 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519340897/1000000000 : ℝ)^4707 ≤ (21642558242387/50000000000000 : ℝ)^3683 := by
    have hnat : (519340897 : ℕ)^4707*50000000000000^3683 ≤ 21642558242387^3683*1000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519340897 1000000000 21642558242387 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081725079/2000000000 : ℝ), (-1793708957/10000000000 : ℝ), (519340897/1000000000 : ℝ)] ![(356177073221/781250000000 : ℝ), (5562109066783/50000000000000 : ℝ), (21642558242387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081725079/2000000000 : ℝ)|^4707 ≤ (356177073221/781250000000 : ℝ)^3683
        have hw : |(1081725079/2000000000 : ℝ)|=(1081725079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1793708957/10000000000 : ℝ)|^4707 ≤ (5562109066783/50000000000000 : ℝ)^3683
        have hw : |(-1793708957/10000000000 : ℝ)|=(1793708957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519340897/1000000000 : ℝ)|^4707 ≤ (21642558242387/50000000000000 : ℝ)^3683
        have hw : |(519340897/1000000000 : ℝ)|=(519340897/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_14 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2704314111/5000000000 : ℝ)*x 0 + (259670427/500000000 : ℝ)*x 1 + (-1793705691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704314111/5000000000 : ℝ)^4707 ≤ (7123546223/15625000000 : ℝ)^3683 := by
    have hnat : (2704314111 : ℕ)^4707*15625000000^3683 ≤ 7123546223^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704314111 5000000000 7123546223 15625000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259670427/500000000 : ℝ)^4707 ≤ (43285111904441/100000000000000 : ℝ)^3683 := by
    have hnat : (259670427 : ℕ)^4707*100000000000000^3683 ≤ 43285111904441^3683*500000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259670427 500000000 43285111904441 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1793705691/10000000000 : ℝ)^4707 ≤ (11124192246903/100000000000000 : ℝ)^3683 := by
    have hnat : (1793705691 : ℕ)^4707*100000000000000^3683 ≤ 11124192246903^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793705691 10000000000 11124192246903 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2704314111/5000000000 : ℝ), (259670427/500000000 : ℝ), (-1793705691/10000000000 : ℝ)] ![(7123546223/15625000000 : ℝ), (43285111904441/100000000000000 : ℝ), (11124192246903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2704314111/5000000000 : ℝ)|^4707 ≤ (7123546223/15625000000 : ℝ)^3683
        have hw : |(2704314111/5000000000 : ℝ)|=(2704314111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259670427/500000000 : ℝ)|^4707 ≤ (43285111904441/100000000000000 : ℝ)^3683
        have hw : |(259670427/500000000 : ℝ)|=(259670427/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1793705691/10000000000 : ℝ)|^4707 ≤ (11124192246903/100000000000000 : ℝ)^3683
        have hw : |(-1793705691/10000000000 : ℝ)|=(1793705691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_box_15 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (24255603/62500000 : ℝ)*x 0 + (4406394623/10000000000 : ℝ)*x 1 + (4406398587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24255603/62500000 : ℝ)^4707 ≤ (29829165760319/100000000000000 : ℝ)^3683 := by
    have hnat : (24255603 : ℕ)^4707*100000000000000^3683 ≤ 29829165760319^3683*62500000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24255603 62500000 29829165760319 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4406394623/10000000000 : ℝ)^4707 ≤ (35085396940569/100000000000000 : ℝ)^3683 := by
    have hnat : (4406394623 : ℕ)^4707*100000000000000^3683 ≤ 35085396940569^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4406394623 10000000000 35085396940569 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4406398587/10000000000 : ℝ)^4707 ≤ (35085437279017/100000000000000 : ℝ)^3683 := by
    have hnat : (4406398587 : ℕ)^4707*100000000000000^3683 ≤ 35085437279017^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4406398587 10000000000 35085437279017 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(24255603/62500000 : ℝ), (4406394623/10000000000 : ℝ), (4406398587/10000000000 : ℝ)] ![(29829165760319/100000000000000 : ℝ), (35085396940569/100000000000000 : ℝ), (35085437279017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(24255603/62500000 : ℝ)|^4707 ≤ (29829165760319/100000000000000 : ℝ)^3683
        have hw : |(24255603/62500000 : ℝ)|=(24255603/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4406394623/10000000000 : ℝ)|^4707 ≤ (35085396940569/100000000000000 : ℝ)^3683
        have hw : |(4406394623/10000000000 : ℝ)|=(4406394623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4406398587/10000000000 : ℝ)|^4707 ≤ (35085437279017/100000000000000 : ℝ)^3683
        have hw : |(4406398587/10000000000 : ℝ)|=(4406398587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1597_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(811/1250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58053/100000 : ℝ) ∧ (8017/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8769/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8181/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8181/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8181/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8181/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8181/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8181/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10347/100000 : ℝ) ^ (4703/1024 : ℝ) ≤ (1493605743903587/50000000000000000000 : ℝ) := by
    have hpowers : (10347/100000 : ℝ)^4703 ≤ (1493605743903587/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10347 : ℕ)^4703*50000000000000000000^1024 ≤ 1493605743903587^1024*100000^4703 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10347 100000 1493605743903587 50000000000000000000 4703 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10347/100000 : ℝ)) (X := (1493605743903587/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8181/50000 : ℝ) ^ (4703/1024 : ℝ) ≤ (24509172404044099/100000000000000000000 : ℝ) := by
    have hpowers : (8181/50000 : ℝ)^4703 ≤ (24509172404044099/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8181 : ℕ)^4703*100000000000000000000^1024 ≤ 24509172404044099^1024*50000^4703 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8181 50000 24509172404044099 100000000000000000000 4703 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8181/50000 : ℝ)) (X := (24509172404044099/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001493605743903587/25000000000000000000 : ℝ) ≤ (156252032501253/156250000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (25001493605743903587/25000000000000000000 : ℝ)^1024 ≤ (156252032501253/156250000000000 : ℝ)^4703 := by
      have hnat : (25001493605743903587 : ℕ)^1024*156250000000000^4703 ≤ 156252032501253^4703*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001493605743903587 25000000000000000000 156252032501253 156250000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156252032501253/156250000000000 : ℝ)) (X := (25001493605743903587/25000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027496383891851273/100000000000000000000 : ℝ) ≤ (10000598623632999/10000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (100027496383891851273/100000000000000000000 : ℝ)^1024 ≤ (10000598623632999/10000000000000000 : ℝ)^4703 := by
      have hnat : (100027496383891851273 : ℕ)^1024*10000000000000000^4703 ≤ 10000598623632999^4703*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027496383891851273 100000000000000000000 10000598623632999 10000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000598623632999/10000000000000000 : ℝ)) (X := (100027496383891851273/100000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024509172404044099/50000000000000000000 : ℝ) ≤ (5000533583592903/5000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (50024509172404044099/50000000000000000000 : ℝ)^1024 ≤ (5000533583592903/5000000000000000 : ℝ)^4703 := by
      have hnat : (50024509172404044099 : ℕ)^1024*5000000000000000^4703 ≤ 5000533583592903^4703*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024509172404044099 50000000000000000000 5000533583592903 5000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000533583592903/5000000000000000 : ℝ)) (X := (50024509172404044099/50000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1493605743903587/50000000000000000000 : ℝ) ≤ ((10023514398566761137/10025000000000000000 : ℝ)+2*(156181184269/200500000000000 : ℝ)*(10347/100000 : ℝ))^(4703/1024 : ℝ) := by
    rw [show (10023514398566761137/10025000000000000000 : ℝ)+2*(156181184269/200500000000000 : ℝ)*(10347/100000 : ℝ)=(156252032501253/156250000000000 : ℝ) by norm_num, show 1+2*(1493605743903587/50000000000000000000 : ℝ)=(25001493605743903587/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24509172404044099/100000000000000000000 : ℝ)+(1493605743903587/50000000000000000000 : ℝ) ≤ ((10023514398566761137/10025000000000000000 : ℝ)+(156181184269/200500000000000 : ℝ)*((8181/50000 : ℝ)+(10347/100000 : ℝ)))^(4703/1024 : ℝ) := by
    rw [show (10023514398566761137/10025000000000000000 : ℝ)+(156181184269/200500000000000 : ℝ)*((8181/50000 : ℝ)+(10347/100000 : ℝ))=(10000598623632999/10000000000000000 : ℝ) by norm_num, show 1+(24509172404044099/100000000000000000000 : ℝ)+(1493605743903587/50000000000000000000 : ℝ)=(100027496383891851273/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24509172404044099/100000000000000000000 : ℝ) ≤ ((10023514398566761137/10025000000000000000 : ℝ)+2*(156181184269/200500000000000 : ℝ)*(8181/50000 : ℝ))^(4703/1024 : ℝ) := by
    rw [show (10023514398566761137/10025000000000000000 : ℝ)+2*(156181184269/200500000000000 : ℝ)*(8181/50000 : ℝ)=(5000533583592903/5000000000000000 : ℝ) by norm_num, show 1+2*(24509172404044099/100000000000000000000 : ℝ)=(50024509172404044099/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10023514398566761137/10025000000000000000 : ℝ)*(X 1 0+X 2 0)+(156181184269/200500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (10347/100000 : ℝ)) (hi := (8181/50000 : ℝ)) (c := (10023514398566761137/10025000000000000000 : ℝ)) (alpha := (156181184269/200500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10023514398566761137/10025000000000000000 : ℝ)*(X 0 1+X 2 1)+(156181184269/200500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (10347/100000 : ℝ)) (hi := (8181/50000 : ℝ)) (c := (10023514398566761137/10025000000000000000 : ℝ)) (alpha := (156181184269/200500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10023514398566761137/10025000000000000000 : ℝ)*(X 0 2+X 1 2)+(156181184269/200500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (10347/100000 : ℝ)) (hi := (8181/50000 : ℝ)) (c := (10023514398566761137/10025000000000000000 : ℝ)) (alpha := (156181184269/200500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-291772289/2000000000 : ℝ)*X 0 0+(5421442521/10000000000 : ℝ)*X 0 1+(1084288417/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((656368061/1250000000 : ℝ)*X 1 0+(-849062343/5000000000 : ℝ)*X 1 1+(5421442191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5250944183/10000000000 : ℝ)*X 2 0+(2710721149/5000000000 : ℝ)*X 2 1+(-339624991/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((900887453/2000000000 : ℝ)*X 0 0+(819173661/2000000000 : ℝ)*X 0 1+(819173533/2000000000 : ℝ)*X 0 2+(900887453/2000000000 : ℝ)*X 1 0+(819173661/2000000000 : ℝ)*X 1 1+(819173533/2000000000 : ℝ)*X 1 2+(900887453/2000000000 : ℝ)*X 2 0+(819173661/2000000000 : ℝ)*X 2 1+(819173533/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1013529957/5000000000 : ℝ)*X 0 0+(5213278431/10000000000 : ℝ)*X 0 1+(1042655781/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5394880319/10000000000 : ℝ)*X 1 0+(-892830661/5000000000 : ℝ)*X 1 1+(1042655827/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5394881607/10000000000 : ℝ)*X 2 0+(5213277643/10000000000 : ℝ)*X 2 1+(-1785661581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((787340887/2000000000 : ℝ)*X 0 0+(27371147/62500000 : ℝ)*X 0 1+(4379384381/10000000000 : ℝ)*X 0 2+(787340887/2000000000 : ℝ)*X 1 0+(27371147/62500000 : ℝ)*X 1 1+(4379384381/10000000000 : ℝ)*X 1 2+(787340887/2000000000 : ℝ)*X 2 0+(27371147/62500000 : ℝ)*X 2 1+(4379384381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1906410773/10000000000 : ℝ)*X 0 0+(5064928797/10000000000 : ℝ)*X 0 1+(5451542829/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2615062137/5000000000 : ℝ)*X 1 0+(-336998619/2000000000 : ℝ)*X 1 1+(340721419/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2615062381/5000000000 : ℝ)*X 2 0+(5451542947/10000000000 : ℝ)*X 2 1+(-168499209/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4584127529/10000000000 : ℝ)*X 0 0+(4054798183/10000000000 : ℝ)*X 0 1+(4054797513/10000000000 : ℝ)*X 0 2+(4584127529/10000000000 : ℝ)*X 1 0+(4054798183/10000000000 : ℝ)*X 1 1+(4054797513/10000000000 : ℝ)*X 1 2+(4584127529/10000000000 : ℝ)*X 2 0+(4054798183/10000000000 : ℝ)*X 2 1+(4054797513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1578493657/10000000000 : ℝ)*X 0 0+(5563633563/10000000000 : ℝ)*X 0 1+(2596704917/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1081725079/2000000000 : ℝ)*X 1 0+(-1793708957/10000000000 : ℝ)*X 1 1+(519340897/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2704314111/5000000000 : ℝ)*X 2 0+(259670427/500000000 : ℝ)*X 2 1+(-1793705691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((24255603/62500000 : ℝ)*X 0 0+(4406394623/10000000000 : ℝ)*X 0 1+(4406398587/10000000000 : ℝ)*X 0 2+(24255603/62500000 : ℝ)*X 1 0+(4406394623/10000000000 : ℝ)*X 1 1+(4406398587/10000000000 : ℝ)*X 1 2+(24255603/62500000 : ℝ)*X 2 0+(4406394623/10000000000 : ℝ)*X 2 1+(4406398587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-811/1250 : ℝ) ≤ (-162598471072938564633946894385349/250625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16910889/100000000000000 : ℝ)*(upper0) + (33274041/100000000000000 : ℝ)*(lower2) + (64572867/100000000000000 : ℝ)*(lower3) + (103866143/100000000000000 : ℝ)*(upper5) + (1656128144968159/100000000000000 : ℝ)*(major0) + (1656128144968159/100000000000000 : ℝ)*(major1) + (1656128144968159/100000000000000 : ℝ)*(major2) + (2625261503/20000000000000 : ℝ)*(sp2) + (1612192741/100000000000000 : ℝ)*(sp3) + (295507727911951/12500000000000 : ℝ)*(sp4) + (11820009807719/500000000000 : ℝ)*(sp5) + (2364048696988093/100000000000000 : ℝ)*(sp6) + (484909293130741/50000000000000 : ℝ)*(sp7) + (59861751807/100000000000000 : ℝ)*(sp13) + (969820198454223/100000000000000 : ℝ)*(f.failure) + (295507727911951/12500000000000 : ℝ)*(f.sum) + (3298251344087/1253125000000000000000000000 : ℝ)*base65 + (1356413323929686783/1002500000000000000000000000000000 : ℝ)*base67 + (5039899120044686783/1002500000000000000000000000000000 : ℝ)*base69 + (11102322028662186783/1002500000000000000000000000000000 : ℝ)*base71 + (277029671062879/10025000000000000000000000000 : ℝ)*base74 + (6492950138669686783/1002500000000000000000000000000000 : ℝ)*base75 + (5710546473334686783/1002500000000000000000000000000000 : ℝ)*base77 + (17216847255122813217/1002500000000000000000000000000000 : ℝ)*base80 + (23622352593523/5012500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (24855689/5000000000000000000000 : ℝ)*base90 + (24855689/5000000000000000000000 : ℝ)*base92 + (24855689/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58053/100000 : ℝ) ≤ (72751327073796760988207873905851/125312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9727199/100000000000000 : ℝ)*(lower0) + (283581/781250000000 : ℝ)*(upper2) + (90988279/100000000000000 : ℝ)*(upper3) + (13540623/25000000000000 : ℝ)*(lower5) + (434775783325347/25000000000000 : ℝ)*(major0) + (434775783325347/25000000000000 : ℝ)*(major1) + (434775783325347/25000000000000 : ℝ)*(major2) + (610111091012637/25000000000000 : ℝ)*(sp0) + (1220211365005537/50000000000000 : ℝ)*(sp1) + (305055130788471/12500000000000 : ℝ)*(sp2) + (254602472988269/25000000000000 : ℝ)*(sp3) + (36647673/100000000000000 : ℝ)*(sp7) + (10817019737/50000000000000 : ℝ)*(sp9) + (165887139/5000000000000 : ℝ)*(sp10) + (1018409928600749/100000000000000 : ℝ)*(f.failure) + (610111091012637/25000000000000 : ℝ)*(f.sum) + (66772466489497/10025000000000000000000000000 : ℝ)*base65 + (926462096281210461/250625000000000000000000000000000 : ℝ)*base68 + (3500741466834335461/250625000000000000000000000000000 : ℝ)*base70 + (1183628968928085461/250625000000000000000000000000000 : ℝ)*base72 + (105805956001639/5012500000000000000000000000 : ℝ)*base74 + (3254880409490585461/250625000000000000000000000000000 : ℝ)*base76 + (379418435375585461/250625000000000000000000000000000 : ℝ)*base78 + (12883728720291210461/250625000000000000000000000000000 : ℝ)*base80 + (21387915277547/10025000000000000000000000000 : ℝ)*base81 + (2259493/5000000000000000000000 : ℝ)*base89 + (2259493/5000000000000000000000 : ℝ)*base91 + (2259493/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (8017/10000 : ℝ) ≤ (40186329731990366699941299468003/50125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67102391/100000000000000 : ℝ)*(upper0) + (1260397/12500000000000 : ℝ)*(lower3) + (301038759/100000000000000 : ℝ)*(upper4) + (369524624589073/20000000000000 : ℝ)*(major0) + (369524624589073/20000000000000 : ℝ)*(major1) + (369524624589073/20000000000000 : ℝ)*(major2) + (50661547/5000000000000 : ℝ)*(sp1) + (42490141537/50000000000000 : ℝ)*(sp2) + (15833605981/50000000000000 : ℝ)*(sp3) + (212358997/20000000000000 : ℝ)*(sp4) + (2586562426516649/100000000000000 : ℝ)*(sp8) + (1293281237540347/50000000000000 : ℝ)*(sp9) + (32330981350357/1250000000000 : ℝ)*(sp10) + (270481753517469/25000000000000 : ℝ)*(sp11) + (540979340640919/50000000000000 : ℝ)*(f.failure) + (1293281744155817/50000000000000 : ℝ)*(f.sum) + (1430507394099/1002500000000000000000000000 : ℝ)*base66 + (1248098506149893999/200500000000000000000000000000000 : ℝ)*base68 + (1759447502278893999/200500000000000000000000000000000 : ℝ)*base70 + (2293023444801893999/200500000000000000000000000000000 : ℝ)*base72 + (31161594461897/2005000000000000000000000000 : ℝ)*base73 + (253531033613893999/200500000000000000000000000000000 : ℝ)*base76 + (1753806040194893999/200500000000000000000000000000000 : ℝ)*base78 + (3328289816758106001/200500000000000000000000000000000 : ℝ)*base79 + (5591495328603/2005000000000000000000000000 : ℝ)*base82 + (6693183/2500000000000000000000 : ℝ)*base89 + (6693183/2500000000000000000000 : ℝ)*base91 + (6693183/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-8769/10000 : ℝ) ≤ (-54941675300689413726517431039351/62656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (462962507/50000000000000 : ℝ)*(lower1) + (1121540747/100000000000000 : ℝ)*(lower2) + (92450321/50000000000000 : ℝ)*(upper5) + (236129390250153/12500000000000 : ℝ)*(major0) + (236129390250153/12500000000000 : ℝ)*(major1) + (236129390250153/12500000000000 : ℝ)*(major2) + (4431276771/25000000000000 : ℝ)*(sp0) + (786852450553/100000000000000 : ℝ)*(sp5) + (263189187717/50000000000000 : ℝ)*(sp6) + (148765821121/100000000000000 : ℝ)*(sp7) + (540214467206881/20000000000000 : ℝ)*(sp12) + (2700303208690937/100000000000000 : ℝ)*(sp13) + (337570460345757/12500000000000 : ℝ)*(sp14) + (1106060570982009/100000000000000 : ℝ)*(sp15) + (110620933680313/10000000000000 : ℝ)*(f.failure) + (270109006114149/10000000000000 : ℝ)*(f.sum) + (10136039391503/5012500000000000000000000000 : ℝ)*base65 + (140192121571571039/125312500000000000000000000000000 : ℝ)*base68 + (484210521317821039/125312500000000000000000000000000 : ℝ)*base70 + (1385709922375008539/125312500000000000000000000000000 : ℝ)*base72 + (4178719017591/626562500000000000000000000 : ℝ)*base73 + (1477819303078758539/125312500000000000000000000000000 : ℝ)*base76 + (767613954421258539/125312500000000000000000000000000 : ℝ)*base78 + (1434480588985008539/125312500000000000000000000000000 : ℝ)*base80 + (17695129770953/5012500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (719441/500000000000000000000 : ℝ)*base89 + (719441/500000000000000000000 : ℝ)*base91 + (719441/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1597_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(811/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(58053/100000 : ℝ) else (8017/10000 : ℝ) ≤ X j i ∧ X j i ≤ (8769/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1597_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1597_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(811/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(58053/100000 : ℝ) else (8017/10000 : ℝ) ≤ X j i ∧ X j i ≤ (8769/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1597_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(811/1250 : ℝ) ≤ X j i ∧ X j i ≤ -(58053/100000 : ℝ) else (8017/10000 : ℝ) ≤ X j i ∧ X j i ≤ (8769/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1597_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
