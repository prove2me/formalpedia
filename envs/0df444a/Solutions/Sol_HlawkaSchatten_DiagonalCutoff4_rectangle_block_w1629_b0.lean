-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1629_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:51.687375+00:00
-- url     : https://prove2.me/submissions/1f46e7a8-bf12-4920-978f-3ed766f1473e

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
theorem support_rectangle_w1629_s0_0 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1530232041/10000000000 : ℝ)*x 0 + (5811929867/10000000000 : ℝ)*x 1 + (2453459967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1530232041/10000000000 : ℝ)^4835 ≤ (9240701337819/100000000000000 : ℝ)^3811 := by
    have hnat : (1530232041 : ℕ)^4835*100000000000000^3811 ≤ 9240701337819^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1530232041 10000000000 9240701337819 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5811929867/10000000000 : ℝ)^4835 ≤ (12558397539701/25000000000000 : ℝ)^3811 := by
    have hnat : (5811929867 : ℕ)^4835*25000000000000^3811 ≤ 12558397539701^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5811929867 10000000000 12558397539701 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2453459967/5000000000 : ℝ)^4835 ≤ (40525708489127/100000000000000 : ℝ)^3811 := by
    have hnat : (2453459967 : ℕ)^4835*100000000000000^3811 ≤ 40525708489127^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2453459967 5000000000 40525708489127 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1530232041/10000000000 : ℝ), (5811929867/10000000000 : ℝ), (2453459967/5000000000 : ℝ)] ![(9240701337819/100000000000000 : ℝ), (12558397539701/25000000000000 : ℝ), (40525708489127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1530232041/10000000000 : ℝ)|^4835 ≤ (9240701337819/100000000000000 : ℝ)^3811
        have hw : |(-1530232041/10000000000 : ℝ)|=(1530232041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5811929867/10000000000 : ℝ)|^4835 ≤ (12558397539701/25000000000000 : ℝ)^3811
        have hw : |(5811929867/10000000000 : ℝ)|=(5811929867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2453459967/5000000000 : ℝ)|^4835 ≤ (40525708489127/100000000000000 : ℝ)^3811
        have hw : |(2453459967/5000000000 : ℝ)|=(2453459967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s0_1 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2722976541/5000000000 : ℝ)*x 0 + (-2029214939/10000000000 : ℝ)*x 1 + (4906921359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2722976541/5000000000 : ℝ)^4835 ≤ (46254931111161/100000000000000 : ℝ)^3811 := by
    have hnat : (2722976541 : ℕ)^4835*100000000000000^3811 ≤ 46254931111161^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722976541 5000000000 46254931111161 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2029214939/10000000000 : ℝ)^4835 ≤ (1652418181179/12500000000000 : ℝ)^3811 := by
    have hnat : (2029214939 : ℕ)^4835*12500000000000^3811 ≤ 1652418181179^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029214939 10000000000 1652418181179 12500000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4906921359/10000000000 : ℝ)^4835 ≤ (8105144684061/20000000000000 : ℝ)^3811 := by
    have hnat : (4906921359 : ℕ)^4835*20000000000000^3811 ≤ 8105144684061^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4906921359 10000000000 8105144684061 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2722976541/5000000000 : ℝ), (-2029214939/10000000000 : ℝ), (4906921359/10000000000 : ℝ)] ![(46254931111161/100000000000000 : ℝ), (1652418181179/12500000000000 : ℝ), (8105144684061/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2722976541/5000000000 : ℝ)|^4835 ≤ (46254931111161/100000000000000 : ℝ)^3811
        have hw : |(2722976541/5000000000 : ℝ)|=(2722976541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2029214939/10000000000 : ℝ)|^4835 ≤ (1652418181179/12500000000000 : ℝ)^3811
        have hw : |(-2029214939/10000000000 : ℝ)|=(2029214939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4906921359/10000000000 : ℝ)|^4835 ≤ (8105144684061/20000000000000 : ℝ)^3811
        have hw : |(4906921359/10000000000 : ℝ)|=(4906921359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s0_2 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2722976629/5000000000 : ℝ)*x 0 + (4906920423/10000000000 : ℝ)*x 1 + (-2029215897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2722976629/5000000000 : ℝ)^4835 ≤ (11563733251917/25000000000000 : ℝ)^3811 := by
    have hnat : (2722976629 : ℕ)^4835*25000000000000^3811 ≤ 11563733251917^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722976629 5000000000 11563733251917 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4906920423/10000000000 : ℝ)^4835 ≤ (40525713612879/100000000000000 : ℝ)^3811 := by
    have hnat : (4906920423 : ℕ)^4835*100000000000000^3811 ≤ 40525713612879^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4906920423 10000000000 40525713612879 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2029215897/10000000000 : ℝ)^4835 ≤ (330483834181/2500000000000 : ℝ)^3811 := by
    have hnat : (2029215897 : ℕ)^4835*2500000000000^3811 ≤ 330483834181^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029215897 10000000000 330483834181 2500000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2722976629/5000000000 : ℝ), (4906920423/10000000000 : ℝ), (-2029215897/10000000000 : ℝ)] ![(11563733251917/25000000000000 : ℝ), (40525713612879/100000000000000 : ℝ), (330483834181/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2722976629/5000000000 : ℝ)|^4835 ≤ (11563733251917/25000000000000 : ℝ)^3811
        have hw : |(2722976629/5000000000 : ℝ)|=(2722976629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4906920423/10000000000 : ℝ)|^4835 ≤ (40525713612879/100000000000000 : ℝ)^3811
        have hw : |(4906920423/10000000000 : ℝ)|=(4906920423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2029215897/10000000000 : ℝ)|^4835 ≤ (330483834181/2500000000000 : ℝ)^3811
        have hw : |(-2029215897/10000000000 : ℝ)|=(2029215897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s0_3 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (128142609/312500000 : ℝ)*x 0 + (769453371/2500000000 : ℝ)*x 1 + (5357471913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128142609/312500000 : ℝ)^4835 ≤ (32271280230967/100000000000000 : ℝ)^3811 := by
    have hnat : (128142609 : ℕ)^4835*100000000000000^3811 ≤ 32271280230967^3811*312500000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128142609 312500000 32271280230967 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (769453371/2500000000 : ℝ)^4835 ≤ (22425137350303/100000000000000 : ℝ)^3811 := by
    have hnat : (769453371 : ℕ)^4835*100000000000000^3811 ≤ 22425137350303^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769453371 2500000000 22425137350303 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5357471913/10000000000 : ℝ)^4835 ≤ (22651791200111/50000000000000 : ℝ)^3811 := by
    have hnat : (5357471913 : ℕ)^4835*50000000000000^3811 ≤ 22651791200111^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357471913 10000000000 22651791200111 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(128142609/312500000 : ℝ), (769453371/2500000000 : ℝ), (5357471913/10000000000 : ℝ)] ![(32271280230967/100000000000000 : ℝ), (22425137350303/100000000000000 : ℝ), (22651791200111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(128142609/312500000 : ℝ)|^4835 ≤ (32271280230967/100000000000000 : ℝ)^3811
        have hw : |(128142609/312500000 : ℝ)|=(128142609/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(769453371/2500000000 : ℝ)|^4835 ≤ (22425137350303/100000000000000 : ℝ)^3811
        have hw : |(769453371/2500000000 : ℝ)|=(769453371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5357471913/10000000000 : ℝ)|^4835 ≤ (22651791200111/50000000000000 : ℝ)^3811
        have hw : |(5357471913/10000000000 : ℝ)|=(5357471913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s0_4 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1532778739/10000000000 : ℝ)*x 0 + (2464808243/5000000000 : ℝ)*x 1 + (5788436519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1532778739/10000000000 : ℝ)^4835 ≤ (9260216837383/100000000000000 : ℝ)^3811 := by
    have hnat : (1532778739 : ℕ)^4835*100000000000000^3811 ≤ 9260216837383^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1532778739 10000000000 9260216837383 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2464808243/5000000000 : ℝ)^4835 ≤ (40763671003609/100000000000000 : ℝ)^3811 := by
    have hnat : (2464808243 : ℕ)^4835*100000000000000^3811 ≤ 40763671003609^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2464808243 5000000000 40763671003609 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5788436519/10000000000 : ℝ)^4835 ≤ (24988056073989/50000000000000 : ℝ)^3811 := by
    have hnat : (5788436519 : ℕ)^4835*50000000000000^3811 ≤ 24988056073989^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5788436519 10000000000 24988056073989 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1532778739/10000000000 : ℝ), (2464808243/5000000000 : ℝ), (5788436519/10000000000 : ℝ)] ![(9260216837383/100000000000000 : ℝ), (40763671003609/100000000000000 : ℝ), (24988056073989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1532778739/10000000000 : ℝ)|^4835 ≤ (9260216837383/100000000000000 : ℝ)^3811
        have hw : |(-1532778739/10000000000 : ℝ)|=(1532778739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2464808243/5000000000 : ℝ)|^4835 ≤ (40763671003609/100000000000000 : ℝ)^3811
        have hw : |(2464808243/5000000000 : ℝ)|=(2464808243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5788436519/10000000000 : ℝ)|^4835 ≤ (24988056073989/50000000000000 : ℝ)^3811
        have hw : |(5788436519/10000000000 : ℝ)|=(5788436519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s0_5 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198855847/10000000000 : ℝ)*x 0 + (-1147700171/10000000000 : ℝ)*x 1 + (2894218007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198855847/10000000000 : ℝ)^4835 ≤ (10902180645893/25000000000000 : ℝ)^3811 := by
    have hnat : (5198855847 : ℕ)^4835*25000000000000^3811 ≤ 10902180645893^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198855847 10000000000 10902180645893 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1147700171/10000000000 : ℝ)^4835 ≤ (320758539537/5000000000000 : ℝ)^3811 := by
    have hnat : (1147700171 : ℕ)^4835*5000000000000^3811 ≤ 320758539537^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147700171 10000000000 320758539537 5000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2894218007/5000000000 : ℝ)^4835 ≤ (49976106616387/100000000000000 : ℝ)^3811 := by
    have hnat : (2894218007 : ℕ)^4835*100000000000000^3811 ≤ 49976106616387^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2894218007 5000000000 49976106616387 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198855847/10000000000 : ℝ), (-1147700171/10000000000 : ℝ), (2894218007/5000000000 : ℝ)] ![(10902180645893/25000000000000 : ℝ), (320758539537/5000000000000 : ℝ), (49976106616387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198855847/10000000000 : ℝ)|^4835 ≤ (10902180645893/25000000000000 : ℝ)^3811
        have hw : |(5198855847/10000000000 : ℝ)|=(5198855847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1147700171/10000000000 : ℝ)|^4835 ≤ (320758539537/5000000000000 : ℝ)^3811
        have hw : |(-1147700171/10000000000 : ℝ)|=(1147700171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2894218007/5000000000 : ℝ)|^4835 ≤ (49976106616387/100000000000000 : ℝ)^3811
        have hw : |(2894218007/5000000000 : ℝ)|=(2894218007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s0_6 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519885449/1000000000 : ℝ)*x 0 + (361777381/625000000 : ℝ)*x 1 + (-1147698991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519885449/1000000000 : ℝ)^4835 ≤ (43608708142383/100000000000000 : ℝ)^3811 := by
    have hnat : (519885449 : ℕ)^4835*100000000000000^3811 ≤ 43608708142383^3811*1000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519885449 1000000000 43608708142383 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (361777381/625000000 : ℝ)^4835 ≤ (1249403235547/2500000000000 : ℝ)^3811 := by
    have hnat : (361777381 : ℕ)^4835*2500000000000^3811 ≤ 1249403235547^3811*625000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361777381 625000000 1249403235547 2500000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147698991/10000000000 : ℝ)^4835 ≤ (3207581211393/50000000000000 : ℝ)^3811 := by
    have hnat : (1147698991 : ℕ)^4835*50000000000000^3811 ≤ 3207581211393^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147698991 10000000000 3207581211393 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519885449/1000000000 : ℝ), (361777381/625000000 : ℝ), (-1147698991/10000000000 : ℝ)] ![(43608708142383/100000000000000 : ℝ), (1249403235547/2500000000000 : ℝ), (3207581211393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519885449/1000000000 : ℝ)|^4835 ≤ (43608708142383/100000000000000 : ℝ)^3811
        have hw : |(519885449/1000000000 : ℝ)|=(519885449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(361777381/625000000 : ℝ)|^4835 ≤ (1249403235547/2500000000000 : ℝ)^3811
        have hw : |(361777381/625000000 : ℝ)|=(361777381/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1147698991/10000000000 : ℝ)|^4835 ≤ (3207581211393/50000000000000 : ℝ)^3811
        have hw : |(-1147698991/10000000000 : ℝ)|=(1147698991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s0_7 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (821395117/2000000000 : ℝ)*x 0 + (1325075217/2500000000 : ℝ)*x 1 + (78424771/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (821395117/2000000000 : ℝ)^4835 ≤ (16167657913803/50000000000000 : ℝ)^3811 := by
    have hnat : (821395117 : ℕ)^4835*50000000000000^3811 ≤ 16167657913803^3811*2000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821395117 2000000000 16167657913803 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1325075217/2500000000 : ℝ)^4835 ≤ (44691116950721/100000000000000 : ℝ)^3811 := by
    have hnat : (1325075217 : ℕ)^4835*100000000000000^3811 ≤ 44691116950721^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325075217 2500000000 44691116950721 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78424771/250000000 : ℝ)^4835 ≤ (4594713440657/20000000000000 : ℝ)^3811 := by
    have hnat : (78424771 : ℕ)^4835*20000000000000^3811 ≤ 4594713440657^3811*250000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78424771 250000000 4594713440657 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(821395117/2000000000 : ℝ), (1325075217/2500000000 : ℝ), (78424771/250000000 : ℝ)] ![(16167657913803/50000000000000 : ℝ), (44691116950721/100000000000000 : ℝ), (4594713440657/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(821395117/2000000000 : ℝ)|^4835 ≤ (16167657913803/50000000000000 : ℝ)^3811
        have hw : |(821395117/2000000000 : ℝ)|=(821395117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1325075217/2500000000 : ℝ)|^4835 ≤ (44691116950721/100000000000000 : ℝ)^3811
        have hw : |(1325075217/2500000000 : ℝ)|=(1325075217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(78424771/250000000 : ℝ)|^4835 ≤ (4594713440657/20000000000000 : ℝ)^3811
        have hw : |(78424771/250000000 : ℝ)|=(78424771/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1629_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (177/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23813/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (4831/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4831 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4831*1^1024 ≤ 0^1024*1^4831 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4831 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4831/1024 : ℝ) ≤ (663100265354197677/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4831 ≤ (663100265354197677/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4831*50000000000000000000^1024 ≤ 663100265354197677^1024*5^4831 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 663100265354197677 50000000000000000000 4831 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (663100265354197677/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4831 := by
      have hnat : (1 : ℕ)^1024*1^4831 ≤ 1^4831*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50663100265354197677/50000000000000000000 : ℝ) ≤ (10027964988312213/10000000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (50663100265354197677/50000000000000000000 : ℝ)^1024 ≤ (10027964988312213/10000000000000000 : ℝ)^4831 := by
      have hnat : (50663100265354197677 : ℕ)^1024*10000000000000000^4831 ≤ 10027964988312213^4831*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50663100265354197677 50000000000000000000 10027964988312213 10000000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027964988312213/10000000000000000 : ℝ)) (X := (50663100265354197677/50000000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25663100265354197677/25000000000000000000 : ℝ) ≤ (5027964988312213/5000000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (25663100265354197677/25000000000000000000 : ℝ)^1024 ≤ (5027964988312213/5000000000000000 : ℝ)^4831 := by
      have hnat : (25663100265354197677 : ℕ)^1024*5000000000000000^4831 ≤ 5027964988312213^4831*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25663100265354197677 25000000000000000000 5027964988312213 5000000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027964988312213/5000000000000000 : ℝ)) (X := (25663100265354197677/25000000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(27964988312213/4000000000000000 : ℝ)*(0 : ℝ))^(4831/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27964988312213/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(663100265354197677/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(27964988312213/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4831/1024 : ℝ) := by
    rw [show (1 : ℝ)+(27964988312213/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10027964988312213/10000000000000000 : ℝ) by norm_num, show 1+(663100265354197677/50000000000000000000 : ℝ)+(0 : ℝ)=(50663100265354197677/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(663100265354197677/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(27964988312213/4000000000000000 : ℝ)*(2/5 : ℝ))^(4831/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27964988312213/4000000000000000 : ℝ)*(2/5 : ℝ)=(5027964988312213/5000000000000000 : ℝ) by norm_num, show 1+2*(663100265354197677/50000000000000000000 : ℝ)=(25663100265354197677/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(27964988312213/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27964988312213/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(27964988312213/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27964988312213/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(27964988312213/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27964988312213/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1530232041/10000000000 : ℝ)*X 0 0+(5811929867/10000000000 : ℝ)*X 0 1+(2453459967/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2722976541/5000000000 : ℝ)*X 1 0+(-2029214939/10000000000 : ℝ)*X 1 1+(4906921359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2722976629/5000000000 : ℝ)*X 2 0+(4906920423/10000000000 : ℝ)*X 2 1+(-2029215897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((128142609/312500000 : ℝ)*X 0 0+(769453371/2500000000 : ℝ)*X 0 1+(5357471913/10000000000 : ℝ)*X 0 2+(128142609/312500000 : ℝ)*X 1 0+(769453371/2500000000 : ℝ)*X 1 1+(5357471913/10000000000 : ℝ)*X 1 2+(128142609/312500000 : ℝ)*X 2 0+(769453371/2500000000 : ℝ)*X 2 1+(5357471913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1532778739/10000000000 : ℝ)*X 0 0+(2464808243/5000000000 : ℝ)*X 0 1+(5788436519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5198855847/10000000000 : ℝ)*X 1 0+(-1147700171/10000000000 : ℝ)*X 1 1+(2894218007/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((519885449/1000000000 : ℝ)*X 2 0+(361777381/625000000 : ℝ)*X 2 1+(-1147698991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((821395117/2000000000 : ℝ)*X 0 0+(1325075217/2500000000 : ℝ)*X 0 1+(78424771/250000000 : ℝ)*X 0 2+(821395117/2000000000 : ℝ)*X 1 0+(1325075217/2500000000 : ℝ)*X 1 1+(78424771/250000000 : ℝ)*X 1 2+(821395117/2000000000 : ℝ)*X 2 0+(1325075217/2500000000 : ℝ)*X 2 1+(78424771/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (247911802638530746658073/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18547309/50000000000000 : ℝ)*(base16) + (76253579/25000000000000 : ℝ)*(base19) + (113078929/25000000000000 : ℝ)*(base23) + (8114143/20000000000000 : ℝ)*(upper2) + (24275629/20000000000000 : ℝ)*(upper3) + (771814975928531/100000000000000 : ℝ)*(major0) + (771814975928531/100000000000000 : ℝ)*(major1) + (771814975928531/100000000000000 : ℝ)*(major2) + (1104963341223151/100000000000000 : ℝ)*(sp0) + (276241241044307/25000000000000 : ℝ)*(sp1) + (220992970794089/20000000000000 : ℝ)*(sp2) + (438663185881357/100000000000000 : ℝ)*(sp3) + (1965063011/100000000000000 : ℝ)*(sp4) + (344263067/25000000000000 : ℝ)*(sp7) + (219332281466813/50000000000000 : ℝ)*(f.failure) + (552482653143081/50000000000000 : ℝ)*(f.sum) + (785019067249103/200000000000000000000000000000 : ℝ)*base65 + (717857532449103/400000000000000000000000000000 : ℝ)*base67 + (1212255480849103/400000000000000000000000000000 : ℝ)*base69 + (1135437525649103/400000000000000000000000000000 : ℝ)*base71 + (435476738449103/200000000000000000000000000000 : ℝ)*base73 + (675486637249103/400000000000000000000000000000 : ℝ)*base75 + (3230380280049103/400000000000000000000000000000 : ℝ)*base77 + (4499558343649103/400000000000000000000000000000 : ℝ)*base79 + (600774823249103/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (33772191/5000000000000000000000 : ℝ)*base89 + (33772191/5000000000000000000000 : ℝ)*base91 + (33772191/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (392829925513628693606079/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (932056727/100000000000000 : ℝ)*(base19) + (755151571/50000000000000 : ℝ)*(base23) + (115759393/12500000000000 : ℝ)*(base39) + (32325641/100000000000000 : ℝ)*(upper3) + (538318619/100000000000000 : ℝ)*(upper5) + (203329477964961/25000000000000 : ℝ)*(major0) + (203329477964961/25000000000000 : ℝ)*(major1) + (8133169857847/1000000000000 : ℝ)*(major2) + (683856443/20000000000000 : ℝ)*(sp1) + (137878697/5000000000000 : ℝ)*(sp2) + (232876337966561/20000000000000 : ℝ)*(sp4) + (145547167311733/12500000000000 : ℝ)*(sp5) + (291094587007717/25000000000000 : ℝ)*(sp6) + (231126472962559/50000000000000 : ℝ)*(sp7) + (231126472962559/50000000000000 : ℝ)*(f.failure) + (1164382615907949/100000000000000 : ℝ)*(f.sum) + (747505359251/3125000000000000000000000000 : ℝ)*base66 + (13981561369411/4000000000000000000000000000 : ℝ)*base67 + (109276850868693/100000000000000000000000000000 : ℝ)*base69 + (5183549886589/4000000000000000000000000000 : ℝ)*base72 + (8088023828249/3125000000000000000000000000 : ℝ)*base73 + (356897397731307/100000000000000000000000000000 : ℝ)*base76 + (329264444631307/100000000000000000000000000000 : ℝ)*base78 + (201876705168693/100000000000000000000000000000 : ℝ)*base79 + (7437695231307/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2168587/5000000000000000000000 : ℝ)*base90 + (2168587/5000000000000000000000 : ℝ)*base92 + (2168587/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1629_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (177/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23813/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1629_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1629_s1_0 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1645059931/10000000000 : ℝ)*x 0 + (5512992909/10000000000 : ℝ)*x 1 + (5131420787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1645059931/10000000000 : ℝ)^4835 ≤ (10129149537127/100000000000000 : ℝ)^3811 := by
    have hnat : (1645059931 : ℕ)^4835*100000000000000^3811 ≤ 10129149537127^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1645059931 10000000000 10129149537127 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5512992909/10000000000 : ℝ)^4835 ≤ (23489258485783/50000000000000 : ℝ)^3811 := by
    have hnat : (5512992909 : ℕ)^4835*50000000000000^3811 ≤ 23489258485783^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512992909 10000000000 23489258485783 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5131420787/10000000000 : ℝ)^4835 ≤ (42892333473647/100000000000000 : ℝ)^3811 := by
    have hnat : (5131420787 : ℕ)^4835*100000000000000^3811 ≤ 42892333473647^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131420787 10000000000 42892333473647 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1645059931/10000000000 : ℝ), (5512992909/10000000000 : ℝ), (5131420787/10000000000 : ℝ)] ![(10129149537127/100000000000000 : ℝ), (23489258485783/50000000000000 : ℝ), (42892333473647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1645059931/10000000000 : ℝ)|^4835 ≤ (10129149537127/100000000000000 : ℝ)^3811
        have hw : |(-1645059931/10000000000 : ℝ)|=(1645059931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5512992909/10000000000 : ℝ)|^4835 ≤ (23489258485783/50000000000000 : ℝ)^3811
        have hw : |(5512992909/10000000000 : ℝ)|=(5512992909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5131420787/10000000000 : ℝ)|^4835 ≤ (42892333473647/100000000000000 : ℝ)^3811
        have hw : |(5131420787/10000000000 : ℝ)|=(5131420787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s1_1 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8586299/16000000 : ℝ)*x 0 + (-1844015379/10000000000 : ℝ)*x 1 + (64142757/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8586299/16000000 : ℝ)^4835 ≤ (45399782652083/100000000000000 : ℝ)^3811 := by
    have hnat : (8586299 : ℕ)^4835*100000000000000^3811 ≤ 45399782652083^3811*16000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8586299 16000000 45399782652083 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1844015379/10000000000 : ℝ)^4835 ≤ (2926971567629/25000000000000 : ℝ)^3811 := by
    have hnat : (1844015379 : ℕ)^4835*25000000000000^3811 ≤ 2926971567629^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844015379 10000000000 2926971567629 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64142757/125000000 : ℝ)^4835 ≤ (42892331066373/100000000000000 : ℝ)^3811 := by
    have hnat : (64142757 : ℕ)^4835*100000000000000^3811 ≤ 42892331066373^3811*125000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64142757 125000000 42892331066373 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8586299/16000000 : ℝ), (-1844015379/10000000000 : ℝ), (64142757/125000000 : ℝ)] ![(45399782652083/100000000000000 : ℝ), (2926971567629/25000000000000 : ℝ), (42892331066373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8586299/16000000 : ℝ)|^4835 ≤ (45399782652083/100000000000000 : ℝ)^3811
        have hw : |(8586299/16000000 : ℝ)|=(8586299/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1844015379/10000000000 : ℝ)|^4835 ≤ (2926971567629/25000000000000 : ℝ)^3811
        have hw : |(-1844015379/10000000000 : ℝ)|=(1844015379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(64142757/125000000 : ℝ)|^4835 ≤ (42892331066373/100000000000000 : ℝ)^3811
        have hw : |(64142757/125000000 : ℝ)|=(64142757/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s1_2 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2683218773/5000000000 : ℝ)*x 0 + (1282854931/2500000000 : ℝ)*x 1 + (-368803117/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683218773/5000000000 : ℝ)^4835 ≤ (9079957970799/20000000000000 : ℝ)^3811 := by
    have hnat : (2683218773 : ℕ)^4835*20000000000000^3811 ≤ 9079957970799^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683218773 5000000000 9079957970799 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282854931/2500000000 : ℝ)^4835 ≤ (2144616110041/5000000000000 : ℝ)^3811 := by
    have hnat : (1282854931 : ℕ)^4835*5000000000000^3811 ≤ 2144616110041^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282854931 2500000000 2144616110041 5000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (368803117/2000000000 : ℝ)^4835 ≤ (11707887929869/100000000000000 : ℝ)^3811 := by
    have hnat : (368803117 : ℕ)^4835*100000000000000^3811 ≤ 11707887929869^3811*2000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368803117 2000000000 11707887929869 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683218773/5000000000 : ℝ), (1282854931/2500000000 : ℝ), (-368803117/2000000000 : ℝ)] ![(9079957970799/20000000000000 : ℝ), (2144616110041/5000000000000 : ℝ), (11707887929869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683218773/5000000000 : ℝ)|^4835 ≤ (9079957970799/20000000000000 : ℝ)^3811
        have hw : |(2683218773/5000000000 : ℝ)|=(2683218773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282854931/2500000000 : ℝ)|^4835 ≤ (2144616110041/5000000000000 : ℝ)^3811
        have hw : |(1282854931/2500000000 : ℝ)|=(1282854931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-368803117/2000000000 : ℝ)|^4835 ≤ (11707887929869/100000000000000 : ℝ)^3811
        have hw : |(-368803117/2000000000 : ℝ)|=(368803117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s1_3 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4187923603/10000000000 : ℝ)*x 0 + (1863960649/5000000000 : ℝ)*x 1 + (1172269151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4187923603/10000000000 : ℝ)^4835 ≤ (4143252347661/12500000000000 : ℝ)^3811 := by
    have hnat : (4187923603 : ℕ)^4835*12500000000000^3811 ≤ 4143252347661^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4187923603 10000000000 4143252347661 12500000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1863960649/5000000000 : ℝ)^4835 ≤ (14298537432337/50000000000000 : ℝ)^3811 := by
    have hnat : (1863960649 : ℕ)^4835*50000000000000^3811 ≤ 14298537432337^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863960649 5000000000 14298537432337 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1172269151/2500000000 : ℝ)^4835 ≤ (38256906338703/100000000000000 : ℝ)^3811 := by
    have hnat : (1172269151 : ℕ)^4835*100000000000000^3811 ≤ 38256906338703^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1172269151 2500000000 38256906338703 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4187923603/10000000000 : ℝ), (1863960649/5000000000 : ℝ), (1172269151/2500000000 : ℝ)] ![(4143252347661/12500000000000 : ℝ), (14298537432337/50000000000000 : ℝ), (38256906338703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4187923603/10000000000 : ℝ)|^4835 ≤ (4143252347661/12500000000000 : ℝ)^3811
        have hw : |(4187923603/10000000000 : ℝ)|=(4187923603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1863960649/5000000000 : ℝ)|^4835 ≤ (14298537432337/50000000000000 : ℝ)^3811
        have hw : |(1863960649/5000000000 : ℝ)|=(1863960649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1172269151/2500000000 : ℝ)|^4835 ≤ (38256906338703/100000000000000 : ℝ)^3811
        have hw : |(1172269151/2500000000 : ℝ)|=(1172269151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s1_4 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-822623749/5000000000 : ℝ)*x 0 + (5135430719/10000000000 : ℝ)*x 1 + (5508923169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (822623749/5000000000 : ℝ)^4835 ≤ (10130614787607/100000000000000 : ℝ)^3811 := by
    have hnat : (822623749 : ℕ)^4835*100000000000000^3811 ≤ 10130614787607^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      822623749 5000000000 10130614787607 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5135430719/10000000000 : ℝ)^4835 ≤ (21467431089681/50000000000000 : ℝ)^3811 := by
    have hnat : (5135430719 : ℕ)^4835*50000000000000^3811 ≤ 21467431089681^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135430719 10000000000 21467431089681 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5508923169/10000000000 : ℝ)^4835 ≤ (11733630754771/25000000000000 : ℝ)^3811 := by
    have hnat : (5508923169 : ℕ)^4835*25000000000000^3811 ≤ 11733630754771^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508923169 10000000000 11733630754771 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-822623749/5000000000 : ℝ), (5135430719/10000000000 : ℝ), (5508923169/10000000000 : ℝ)] ![(10130614787607/100000000000000 : ℝ), (21467431089681/50000000000000 : ℝ), (11733630754771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-822623749/5000000000 : ℝ)|^4835 ≤ (10130614787607/100000000000000 : ℝ)^3811
        have hw : |(-822623749/5000000000 : ℝ)|=(822623749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5135430719/10000000000 : ℝ)|^4835 ≤ (21467431089681/50000000000000 : ℝ)^3811
        have hw : |(5135430719/10000000000 : ℝ)|=(5135430719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5508923169/10000000000 : ℝ)|^4835 ≤ (11733630754771/25000000000000 : ℝ)^3811
        have hw : |(5508923169/10000000000 : ℝ)|=(5508923169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s1_5 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264659707/10000000000 : ℝ)*x 0 + (-293302393/2000000000 : ℝ)*x 1 + (5508923517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264659707/10000000000 : ℝ)^4835 ≤ (44310194217437/100000000000000 : ℝ)^3811 := by
    have hnat : (5264659707 : ℕ)^4835*100000000000000^3811 ≤ 44310194217437^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264659707 10000000000 44310194217437 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (293302393/2000000000 : ℝ)^4835 ≤ (8755278975363/100000000000000 : ℝ)^3811 := by
    have hnat : (293302393 : ℕ)^4835*100000000000000^3811 ≤ 8755278975363^3811*2000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293302393 2000000000 8755278975363 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5508923517/10000000000 : ℝ)^4835 ≤ (11733631695149/25000000000000 : ℝ)^3811 := by
    have hnat : (5508923517 : ℕ)^4835*25000000000000^3811 ≤ 11733631695149^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508923517 10000000000 11733631695149 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264659707/10000000000 : ℝ), (-293302393/2000000000 : ℝ), (5508923517/10000000000 : ℝ)] ![(44310194217437/100000000000000 : ℝ), (8755278975363/100000000000000 : ℝ), (11733631695149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264659707/10000000000 : ℝ)|^4835 ≤ (44310194217437/100000000000000 : ℝ)^3811
        have hw : |(5264659707/10000000000 : ℝ)|=(5264659707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-293302393/2000000000 : ℝ)|^4835 ≤ (8755278975363/100000000000000 : ℝ)^3811
        have hw : |(-293302393/2000000000 : ℝ)|=(293302393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5508923517/10000000000 : ℝ)|^4835 ≤ (11733631695149/25000000000000 : ℝ)^3811
        have hw : |(5508923517/10000000000 : ℝ)|=(5508923517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s1_6 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105293181/200000000 : ℝ)*x 0 + (2754461879/5000000000 : ℝ)*x 1 + (-29330251/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105293181/200000000 : ℝ)^4835 ≤ (5538773400247/12500000000000 : ℝ)^3811 := by
    have hnat : (105293181 : ℕ)^4835*12500000000000^3811 ≤ 5538773400247^3811*200000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105293181 200000000 5538773400247 12500000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2754461879/5000000000 : ℝ)^4835 ≤ (46934529385551/100000000000000 : ℝ)^3811 := by
    have hnat : (2754461879 : ℕ)^4835*100000000000000^3811 ≤ 46934529385551^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754461879 5000000000 46934529385551 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29330251/200000000 : ℝ)^4835 ≤ (8755283406323/100000000000000 : ℝ)^3811 := by
    have hnat : (29330251 : ℕ)^4835*100000000000000^3811 ≤ 8755283406323^3811*200000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29330251 200000000 8755283406323 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105293181/200000000 : ℝ), (2754461879/5000000000 : ℝ), (-29330251/200000000 : ℝ)] ![(5538773400247/12500000000000 : ℝ), (46934529385551/100000000000000 : ℝ), (8755283406323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105293181/200000000 : ℝ)|^4835 ≤ (5538773400247/12500000000000 : ℝ)^3811
        have hw : |(105293181/200000000 : ℝ)|=(105293181/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2754461879/5000000000 : ℝ)|^4835 ≤ (46934529385551/100000000000000 : ℝ)^3811
        have hw : |(2754461879/5000000000 : ℝ)|=(2754461879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-29330251/200000000 : ℝ)|^4835 ≤ (8755283406323/100000000000000 : ℝ)^3811
        have hw : |(-29330251/200000000 : ℝ)|=(29330251/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s1_7 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41883933/100000000 : ℝ)*x 0 + (187159067/400000000 : ℝ)*x 1 + (3738171803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41883933/100000000 : ℝ)^4835 ≤ (33150735223103/100000000000000 : ℝ)^3811 := by
    have hnat : (41883933 : ℕ)^4835*100000000000000^3811 ≤ 33150735223103^3811*100000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41883933 100000000 33150735223103 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187159067/400000000 : ℝ)^4835 ≤ (2384524549109/6250000000000 : ℝ)^3811 := by
    have hnat : (187159067 : ℕ)^4835*6250000000000^3811 ≤ 2384524549109^3811*400000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187159067 400000000 2384524549109 6250000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3738171803/10000000000 : ℝ)^4835 ≤ (14348435987317/50000000000000 : ℝ)^3811 := by
    have hnat : (3738171803 : ℕ)^4835*50000000000000^3811 ≤ 14348435987317^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3738171803 10000000000 14348435987317 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41883933/100000000 : ℝ), (187159067/400000000 : ℝ), (3738171803/10000000000 : ℝ)] ![(33150735223103/100000000000000 : ℝ), (2384524549109/6250000000000 : ℝ), (14348435987317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41883933/100000000 : ℝ)|^4835 ≤ (33150735223103/100000000000000 : ℝ)^3811
        have hw : |(41883933/100000000 : ℝ)|=(41883933/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(187159067/400000000 : ℝ)|^4835 ≤ (2384524549109/6250000000000 : ℝ)^3811
        have hw : |(187159067/400000000 : ℝ)|=(187159067/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3738171803/10000000000 : ℝ)|^4835 ≤ (14348435987317/50000000000000 : ℝ)^3811
        have hw : |(3738171803/10000000000 : ℝ)|=(3738171803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1629_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23813/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (177/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (189/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8773/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23813/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (177/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23813/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (177/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23813/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (177/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23813/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (177/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23813/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (177/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23813/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (177/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (177/4000 : ℝ) ^ (4831/1024 : ℝ) ≤ (20450108720329/50000000000000000000 : ℝ) := by
    have hpowers : (177/4000 : ℝ)^4831 ≤ (20450108720329/50000000000000000000 : ℝ)^1024 := by
      have hnat : (177 : ℕ)^4831*50000000000000000000^1024 ≤ 20450108720329^1024*4000^4831 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        177 4000 20450108720329 50000000000000000000 4831 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (177/4000 : ℝ)) (X := (20450108720329/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23813/100000 : ℝ) ^ (4831/1024 : ℝ) ≤ (57401094729017651/50000000000000000000 : ℝ) := by
    have hpowers : (23813/100000 : ℝ)^4831 ≤ (57401094729017651/50000000000000000000 : ℝ)^1024 := by
      have hnat : (23813 : ℕ)^4831*50000000000000000000^1024 ≤ 57401094729017651^1024*100000^4831 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23813 100000 57401094729017651 50000000000000000000 4831 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23813/100000 : ℝ)) (X := (57401094729017651/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000020450108720329/25000000000000000000 : ℝ) ≤ (625000108367339/625000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (25000020450108720329/25000000000000000000 : ℝ)^1024 ≤ (625000108367339/625000000000000 : ℝ)^4831 := by
      have hnat : (25000020450108720329 : ℕ)^1024*625000000000000^4831 ≤ 625000108367339^4831*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000020450108720329 25000000000000000000 625000108367339 625000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000108367339/625000000000000 : ℝ)) (X := (25000020450108720329/25000000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2502871077241886899/2500000000000000000 : ℝ) ≤ (5001216581931977/5000000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (2502871077241886899/2500000000000000000 : ℝ)^1024 ≤ (5001216581931977/5000000000000000 : ℝ)^4831 := by
      have hnat : (2502871077241886899 : ℕ)^1024*5000000000000000^4831 ≤ 5001216581931977^4831*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502871077241886899 2500000000000000000 5001216581931977 5000000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001216581931977/5000000000000000 : ℝ)) (X := (2502871077241886899/2500000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25057401094729017651/25000000000000000000 : ℝ) ≤ (2501216148462621/2500000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (25057401094729017651/25000000000000000000 : ℝ)^1024 ≤ (2501216148462621/2500000000000000 : ℝ)^4831 := by
      have hnat : (25057401094729017651 : ℕ)^1024*2500000000000000^4831 ≤ 2501216148462621^4831*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25057401094729017651 25000000000000000000 2501216148462621 2500000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501216148462621/2500000000000000 : ℝ)) (X := (25057401094729017651/25000000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(20450108720329/50000000000000000000 : ℝ) ≤ ((48464628865258676503/48470000000000000000 : ℝ)+2*(243142998653/193880000000000 : ℝ)*(177/4000 : ℝ))^(4831/1024 : ℝ) := by
    rw [show (48464628865258676503/48470000000000000000 : ℝ)+2*(243142998653/193880000000000 : ℝ)*(177/4000 : ℝ)=(625000108367339/625000000000000 : ℝ) by norm_num, show 1+2*(20450108720329/50000000000000000000 : ℝ)=(25000020450108720329/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(57401094729017651/50000000000000000000 : ℝ)+(20450108720329/50000000000000000000 : ℝ) ≤ ((48464628865258676503/48470000000000000000 : ℝ)+(243142998653/193880000000000 : ℝ)*((23813/100000 : ℝ)+(177/4000 : ℝ)))^(4831/1024 : ℝ) := by
    rw [show (48464628865258676503/48470000000000000000 : ℝ)+(243142998653/193880000000000 : ℝ)*((23813/100000 : ℝ)+(177/4000 : ℝ))=(5001216581931977/5000000000000000 : ℝ) by norm_num, show 1+(57401094729017651/50000000000000000000 : ℝ)+(20450108720329/50000000000000000000 : ℝ)=(2502871077241886899/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(57401094729017651/50000000000000000000 : ℝ) ≤ ((48464628865258676503/48470000000000000000 : ℝ)+2*(243142998653/193880000000000 : ℝ)*(23813/100000 : ℝ))^(4831/1024 : ℝ) := by
    rw [show (48464628865258676503/48470000000000000000 : ℝ)+2*(243142998653/193880000000000 : ℝ)*(23813/100000 : ℝ)=(2501216148462621/2500000000000000 : ℝ) by norm_num, show 1+2*(57401094729017651/50000000000000000000 : ℝ)=(25057401094729017651/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (48464628865258676503/48470000000000000000 : ℝ)*(X 1 0+X 2 0)+(243142998653/193880000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (177/4000 : ℝ)) (hi := (23813/100000 : ℝ)) (c := (48464628865258676503/48470000000000000000 : ℝ)) (alpha := (243142998653/193880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (48464628865258676503/48470000000000000000 : ℝ)*(X 0 1+X 2 1)+(243142998653/193880000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (177/4000 : ℝ)) (hi := (23813/100000 : ℝ)) (c := (48464628865258676503/48470000000000000000 : ℝ)) (alpha := (243142998653/193880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (48464628865258676503/48470000000000000000 : ℝ)*(X 0 2+X 1 2)+(243142998653/193880000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (177/4000 : ℝ)) (hi := (23813/100000 : ℝ)) (c := (48464628865258676503/48470000000000000000 : ℝ)) (alpha := (243142998653/193880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1645059931/10000000000 : ℝ)*X 0 0+(5512992909/10000000000 : ℝ)*X 0 1+(5131420787/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((8586299/16000000 : ℝ)*X 1 0+(-1844015379/10000000000 : ℝ)*X 1 1+(64142757/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2683218773/5000000000 : ℝ)*X 2 0+(1282854931/2500000000 : ℝ)*X 2 1+(-368803117/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4187923603/10000000000 : ℝ)*X 0 0+(1863960649/5000000000 : ℝ)*X 0 1+(1172269151/2500000000 : ℝ)*X 0 2+(4187923603/10000000000 : ℝ)*X 1 0+(1863960649/5000000000 : ℝ)*X 1 1+(1172269151/2500000000 : ℝ)*X 1 2+(4187923603/10000000000 : ℝ)*X 2 0+(1863960649/5000000000 : ℝ)*X 2 1+(1172269151/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-822623749/5000000000 : ℝ)*X 0 0+(5135430719/10000000000 : ℝ)*X 0 1+(5508923169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5264659707/10000000000 : ℝ)*X 1 0+(-293302393/2000000000 : ℝ)*X 1 1+(5508923517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((105293181/200000000 : ℝ)*X 2 0+(2754461879/5000000000 : ℝ)*X 2 1+(-29330251/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((41883933/100000000 : ℝ)*X 0 0+(187159067/400000000 : ℝ)*X 0 1+(3738171803/10000000000 : ℝ)*X 0 2+(41883933/100000000 : ℝ)*X 1 0+(187159067/400000000 : ℝ)*X 1 1+(3738171803/10000000000 : ℝ)*X 1 2+(41883933/100000000 : ℝ)*X 2 0+(187159067/400000000 : ℝ)*X 2 1+(3738171803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2051294515108839616931160621/302937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52658141/12500000000000 : ℝ)*(base1) + (1011463143/100000000000000 : ℝ)*(base19) + (1339150953/100000000000000 : ℝ)*(base23) + (6956879/5000000000000 : ℝ)*(upper3) + (2776709/4000000000000 : ℝ)*(upper5) + (457644854774319/25000000000000 : ℝ)*(major0) + (457644854774319/25000000000000 : ℝ)*(major1) + (1830579419097277/100000000000000 : ℝ)*(major2) + (655184703066191/25000000000000 : ℝ)*(sp0) + (131036971812751/5000000000000 : ℝ)*(sp1) + (2620739108567211/100000000000000 : ℝ)*(sp2) + (8128248027767/781250000000 : ℝ)*(sp3) + (2056718527/100000000000000 : ℝ)*(sp4) + (498986389/25000000000000 : ℝ)*(sp7) + (52020908238243/5000000000000 : ℝ)*(f.failure) + (655185111929541/25000000000000 : ℝ)*(f.sum) + (4821423162743/3877600000000000000000000000 : ℝ)*base66 + (3982114779824061043/1211750000000000000000000000000000 : ℝ)*base68 + (2670594674097182331/4847000000000000000000000000000000 : ℝ)*base69 + (6799090957193311043/1211750000000000000000000000000000 : ℝ)*base72 + (1891978816317/775520000000000000000000000 : ℝ)*base73 + (11832161860945817669/4847000000000000000000000000000000 : ℝ)*base76 + (6987618181854623543/1211750000000000000000000000000000 : ℝ)*base78 + (20780388461646123543/1211750000000000000000000000000000 : ℝ)*base80 + (6166742687/193880000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (332799/500000000000000000000 : ℝ)*base90 + (332799/500000000000000000000 : ℝ)*base92 + (5332799/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (810449254796739160380669009/75734375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2066390937/100000000000000 : ℝ)*(base19) + (1411271/80000000000 : ℝ)*(base23) + (4563751/20000000000000 : ℝ)*(upper2) + (419111383/100000000000000 : ℝ)*(upper3) + (28439893/25000000000000 : ℝ)*(upper5) + (29221443703187/1562500000000 : ℝ)*(major0) + (29221443703187/1562500000000 : ℝ)*(major1) + (29221443703187/1562500000000 : ℝ)*(major2) + (15949409537/100000000000000 : ℝ)*(sp1) + (15353400999/100000000000000 : ℝ)*(sp2) + (535484684580407/20000000000000 : ℝ)*(sp4) + (66935135177539/2500000000000 : ℝ)*(sp5) + (2677406305412287/100000000000000 : ℝ)*(sp6) + (1062921014398977/100000000000000 : ℝ)*(sp7) + (1062921014398977/100000000000000 : ℝ)*(f.failure) + (535484684580407/20000000000000 : ℝ)*(f.sum) + (12241701607531/2423500000000000000000000000 : ℝ)*base65 + (154494149497115061/75734375000000000000000000000000 : ℝ)*base67 + (319945342685416189/75734375000000000000000000000000 : ℝ)*base70 + (159005233901681109/18933593750000000000000000000000 : ℝ)*base71 + (1064753833749/605875000000000000000000000 : ℝ)*base74 + (4217029049666371/4733398437500000000000000000000 : ℝ)*base75 + (473878485050115061/75734375000000000000000000000000 : ℝ)*base77 + (298497880872372157/37867187500000000000000000000000 : ℝ)*base80 + (23869143359/19388000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (92476661/10000000000000000000000 : ℝ)*base90 + (92476661/10000000000000000000000 : ℝ)*base92 + (92476661/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1629_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23813/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (177/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (189/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8773/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1629_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1629_s2_0 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-414141189/2500000000 : ℝ)*x 0 + (545892861/1000000000 : ℝ)*x 1 + (5177925099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414141189/2500000000 : ℝ)^4835 ≤ (2043821349149/20000000000000 : ℝ)^3811 := by
    have hnat : (414141189 : ℕ)^4835*20000000000000^3811 ≤ 2043821349149^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414141189 2500000000 2043821349149 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545892861/1000000000 : ℝ)^4835 ≤ (23197397504203/50000000000000 : ℝ)^3811 := by
    have hnat : (545892861 : ℕ)^4835*50000000000000^3811 ≤ 23197397504203^3811*1000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545892861 1000000000 23197397504203 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177925099/10000000000 : ℝ)^4835 ≤ (542326227893/1250000000000 : ℝ)^3811 := by
    have hnat : (5177925099 : ℕ)^4835*1250000000000^3811 ≤ 542326227893^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177925099 10000000000 542326227893 1250000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-414141189/2500000000 : ℝ), (545892861/1000000000 : ℝ), (5177925099/10000000000 : ℝ)] ![(2043821349149/20000000000000 : ℝ), (23197397504203/50000000000000 : ℝ), (542326227893/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-414141189/2500000000 : ℝ)|^4835 ≤ (2043821349149/20000000000000 : ℝ)^3811
        have hw : |(-414141189/2500000000 : ℝ)|=(414141189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545892861/1000000000 : ℝ)|^4835 ≤ (23197397504203/50000000000000 : ℝ)^3811
        have hw : |(545892861/1000000000 : ℝ)|=(545892861/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177925099/10000000000 : ℝ)|^4835 ≤ (542326227893/1250000000000 : ℝ)^3811
        have hw : |(5177925099/10000000000 : ℝ)|=(5177925099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s2_1 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214089481/400000000 : ℝ)*x 0 + (-72059929/400000000 : ℝ)*x 1 + (5177925147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214089481/400000000 : ℝ)^4835 ≤ (22623714210453/50000000000000 : ℝ)^3811 := by
    have hnat : (214089481 : ℕ)^4835*50000000000000^3811 ≤ 22623714210453^3811*400000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214089481 400000000 22623714210453 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (72059929/400000000 : ℝ)^4835 ≤ (2273294562601/20000000000000 : ℝ)^3811 := by
    have hnat : (72059929 : ℕ)^4835*20000000000000^3811 ≤ 2273294562601^3811*400000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72059929 400000000 2273294562601 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177925147/10000000000 : ℝ)^4835 ≤ (43386098741703/100000000000000 : ℝ)^3811 := by
    have hnat : (5177925147 : ℕ)^4835*100000000000000^3811 ≤ 43386098741703^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177925147 10000000000 43386098741703 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214089481/400000000 : ℝ), (-72059929/400000000 : ℝ), (5177925147/10000000000 : ℝ)] ![(22623714210453/50000000000000 : ℝ), (2273294562601/20000000000000 : ℝ), (43386098741703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214089481/400000000 : ℝ)|^4835 ≤ (22623714210453/50000000000000 : ℝ)^3811
        have hw : |(214089481/400000000 : ℝ)|=(214089481/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-72059929/400000000 : ℝ)|^4835 ≤ (2273294562601/20000000000000 : ℝ)^3811
        have hw : |(-72059929/400000000 : ℝ)|=(72059929/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177925147/10000000000 : ℝ)|^4835 ≤ (43386098741703/100000000000000 : ℝ)^3811
        have hw : |(5177925147/10000000000 : ℝ)|=(5177925147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s2_2 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53522371/100000000 : ℝ)*x 0 + (1035585001/2000000000 : ℝ)*x 1 + (-900749157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53522371/100000000 : ℝ)^4835 ≤ (11311857306329/25000000000000 : ℝ)^3811 := by
    have hnat : (53522371 : ℕ)^4835*25000000000000^3811 ≤ 11311857306329^3811*100000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53522371 100000000 11311857306329 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035585001/2000000000 : ℝ)^4835 ≤ (2711631077011/6250000000000 : ℝ)^3811 := by
    have hnat : (1035585001 : ℕ)^4835*6250000000000^3811 ≤ 2711631077011^3811*2000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035585001 2000000000 2711631077011 6250000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900749157/5000000000 : ℝ)^4835 ≤ (1136647352543/10000000000000 : ℝ)^3811 := by
    have hnat : (900749157 : ℕ)^4835*10000000000000^3811 ≤ 1136647352543^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900749157 5000000000 1136647352543 10000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53522371/100000000 : ℝ), (1035585001/2000000000 : ℝ), (-900749157/5000000000 : ℝ)] ![(11311857306329/25000000000000 : ℝ), (2711631077011/6250000000000 : ℝ), (1136647352543/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53522371/100000000 : ℝ)|^4835 ≤ (11311857306329/25000000000000 : ℝ)^3811
        have hw : |(53522371/100000000 : ℝ)|=(53522371/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035585001/2000000000 : ℝ)|^4835 ≤ (2711631077011/6250000000000 : ℝ)^3811
        have hw : |(1035585001/2000000000 : ℝ)|=(1035585001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-900749157/5000000000 : ℝ)|^4835 ≤ (1136647352543/10000000000000 : ℝ)^3811
        have hw : |(-900749157/5000000000 : ℝ)|=(900749157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s2_3 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4196455219/10000000000 : ℝ)*x 0 + (240856517/625000000 : ℝ)*x 1 + (4561532533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4196455219/10000000000 : ℝ)^4835 ≤ (3323171077343/10000000000000 : ℝ)^3811 := by
    have hnat : (4196455219 : ℕ)^4835*10000000000000^3811 ≤ 3323171077343^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196455219 10000000000 3323171077343 10000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240856517/625000000 : ℝ)^4835 ≤ (29826727904741/100000000000000 : ℝ)^3811 := by
    have hnat : (240856517 : ℕ)^4835*100000000000000^3811 ≤ 29826727904741^3811*625000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240856517 625000000 29826727904741 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4561532533/10000000000 : ℝ)^4835 ≤ (1477662452337/4000000000000 : ℝ)^3811 := by
    have hnat : (4561532533 : ℕ)^4835*4000000000000^3811 ≤ 1477662452337^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4561532533 10000000000 1477662452337 4000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4196455219/10000000000 : ℝ), (240856517/625000000 : ℝ), (4561532533/10000000000 : ℝ)] ![(3323171077343/10000000000000 : ℝ), (29826727904741/100000000000000 : ℝ), (1477662452337/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4196455219/10000000000 : ℝ)|^4835 ≤ (3323171077343/10000000000000 : ℝ)^3811
        have hw : |(4196455219/10000000000 : ℝ)|=(4196455219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(240856517/625000000 : ℝ)|^4835 ≤ (29826727904741/100000000000000 : ℝ)^3811
        have hw : |(240856517/625000000 : ℝ)|=(240856517/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4561532533/10000000000 : ℝ)|^4835 ≤ (1477662452337/4000000000000 : ℝ)^3811
        have hw : |(4561532533/10000000000 : ℝ)|=(4561532533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s2_4 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1656639209/10000000000 : ℝ)*x 0 + (2590053379/5000000000 : ℝ)*x 1 + (5456723429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1656639209/10000000000 : ℝ)^4835 ≤ (10219689448233/100000000000000 : ℝ)^3811 := by
    have hnat : (1656639209 : ℕ)^4835*100000000000000^3811 ≤ 10219689448233^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656639209 10000000000 10219689448233 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590053379/5000000000 : ℝ)^4835 ≤ (10852322899761/25000000000000 : ℝ)^3811 := by
    have hnat : (2590053379 : ℕ)^4835*25000000000000^3811 ≤ 10852322899761^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590053379 5000000000 10852322899761 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456723429/10000000000 : ℝ)^4835 ≤ (46371018939847/100000000000000 : ℝ)^3811 := by
    have hnat : (5456723429 : ℕ)^4835*100000000000000^3811 ≤ 46371018939847^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456723429 10000000000 46371018939847 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1656639209/10000000000 : ℝ), (2590053379/5000000000 : ℝ), (5456723429/10000000000 : ℝ)] ![(10219689448233/100000000000000 : ℝ), (10852322899761/25000000000000 : ℝ), (46371018939847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1656639209/10000000000 : ℝ)|^4835 ≤ (10219689448233/100000000000000 : ℝ)^3811
        have hw : |(-1656639209/10000000000 : ℝ)|=(1656639209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590053379/5000000000 : ℝ)|^4835 ≤ (10852322899761/25000000000000 : ℝ)^3811
        have hw : |(2590053379/5000000000 : ℝ)|=(2590053379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456723429/10000000000 : ℝ)|^4835 ≤ (46371018939847/100000000000000 : ℝ)^3811
        have hw : |(5456723429/10000000000 : ℝ)|=(5456723429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s2_5 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319342221/2500000000 : ℝ)*x 0 + (-1522699837/10000000000 : ℝ)*x 1 + (682090443/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319342221/2500000000 : ℝ)^4835 ≤ (44445947097697/100000000000000 : ℝ)^3811 := by
    have hnat : (1319342221 : ℕ)^4835*100000000000000^3811 ≤ 44445947097697^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319342221 2500000000 44445947097697 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1522699837/10000000000 : ℝ)^4835 ≤ (573939544453/6250000000000 : ℝ)^3811 := by
    have hnat : (1522699837 : ℕ)^4835*6250000000000^3811 ≤ 573939544453^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522699837 10000000000 573939544453 6250000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682090443/1250000000 : ℝ)^4835 ≤ (463710201797/1000000000000 : ℝ)^3811 := by
    have hnat : (682090443 : ℕ)^4835*1000000000000^3811 ≤ 463710201797^3811*1250000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682090443 1250000000 463710201797 1000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319342221/2500000000 : ℝ), (-1522699837/10000000000 : ℝ), (682090443/1250000000 : ℝ)] ![(44445947097697/100000000000000 : ℝ), (573939544453/6250000000000 : ℝ), (463710201797/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319342221/2500000000 : ℝ)|^4835 ≤ (44445947097697/100000000000000 : ℝ)^3811
        have hw : |(1319342221/2500000000 : ℝ)|=(1319342221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1522699837/10000000000 : ℝ)|^4835 ≤ (573939544453/6250000000000 : ℝ)^3811
        have hw : |(-1522699837/10000000000 : ℝ)|=(1522699837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682090443/1250000000 : ℝ)|^4835 ≤ (463710201797/1000000000000 : ℝ)^3811
        have hw : |(682090443/1250000000 : ℝ)|=(682090443/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s2_6 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277369863/10000000000 : ℝ)*x 0 + (85261287/156250000 : ℝ)*x 1 + (-1522700127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277369863/10000000000 : ℝ)^4835 ≤ (22222978779129/50000000000000 : ℝ)^3811 := by
    have hnat : (5277369863 : ℕ)^4835*50000000000000^3811 ≤ 22222978779129^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277369863 10000000000 22222978779129 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85261287/156250000 : ℝ)^4835 ≤ (46371007500859/100000000000000 : ℝ)^3811 := by
    have hnat : (85261287 : ℕ)^4835*100000000000000^3811 ≤ 46371007500859^3811*156250000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85261287 156250000 46371007500859 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1522700127/10000000000 : ℝ)^4835 ≤ (1836606986019/20000000000000 : ℝ)^3811 := by
    have hnat : (1522700127 : ℕ)^4835*20000000000000^3811 ≤ 1836606986019^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522700127 10000000000 1836606986019 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277369863/10000000000 : ℝ), (85261287/156250000 : ℝ), (-1522700127/10000000000 : ℝ)] ![(22222978779129/50000000000000 : ℝ), (46371007500859/100000000000000 : ℝ), (1836606986019/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277369863/10000000000 : ℝ)|^4835 ≤ (22222978779129/50000000000000 : ℝ)^3811
        have hw : |(5277369863/10000000000 : ℝ)|=(5277369863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85261287/156250000 : ℝ)|^4835 ≤ (46371007500859/100000000000000 : ℝ)^3811
        have hw : |(85261287/156250000 : ℝ)|=(85261287/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1522700127/10000000000 : ℝ)|^4835 ≤ (1836606986019/20000000000000 : ℝ)^3811
        have hw : |(-1522700127/10000000000 : ℝ)|=(1522700127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s2_7 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1049160841/2500000000 : ℝ)*x 0 + (284752423/625000000 : ℝ)*x 1 + (3859258167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049160841/2500000000 : ℝ)^4835 ≤ (1329344041579/4000000000000 : ℝ)^3811 := by
    have hnat : (1049160841 : ℕ)^4835*4000000000000^3811 ≤ 1329344041579^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049160841 2500000000 1329344041579 4000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284752423/625000000 : ℝ)^4835 ≤ (36885124586427/100000000000000 : ℝ)^3811 := by
    have hnat : (284752423 : ℕ)^4835*100000000000000^3811 ≤ 36885124586427^3811*625000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284752423 625000000 36885124586427 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3859258167/10000000000 : ℝ)^4835 ≤ (14940637176233/50000000000000 : ℝ)^3811 := by
    have hnat : (3859258167 : ℕ)^4835*50000000000000^3811 ≤ 14940637176233^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3859258167 10000000000 14940637176233 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049160841/2500000000 : ℝ), (284752423/625000000 : ℝ), (3859258167/10000000000 : ℝ)] ![(1329344041579/4000000000000 : ℝ), (36885124586427/100000000000000 : ℝ), (14940637176233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049160841/2500000000 : ℝ)|^4835 ≤ (1329344041579/4000000000000 : ℝ)^3811
        have hw : |(1049160841/2500000000 : ℝ)|=(1049160841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(284752423/625000000 : ℝ)|^4835 ≤ (36885124586427/100000000000000 : ℝ)^3811
        have hw : |(284752423/625000000 : ℝ)|=(284752423/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3859258167/10000000000 : ℝ)|^4835 ≤ (14940637176233/50000000000000 : ℝ)^3811
        have hw : |(3859258167/10000000000 : ℝ)|=(3859258167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1629_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8773/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (189/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (5227/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16419/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8773/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (189/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8773/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (189/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8773/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (189/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8773/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (189/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8773/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (189/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8773/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (189/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (189/2000 : ℝ) ^ (4831/1024 : ℝ) ≤ (1466626072537119/100000000000000000000 : ℝ) := by
    have hpowers : (189/2000 : ℝ)^4831 ≤ (1466626072537119/100000000000000000000 : ℝ)^1024 := by
      have hnat : (189 : ℕ)^4831*100000000000000000000^1024 ≤ 1466626072537119^1024*2000^4831 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        189 2000 1466626072537119 100000000000000000000 4831 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (189/2000 : ℝ)) (X := (1466626072537119/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8773/50000 : ℝ) ^ (4831/1024 : ℝ) ≤ (27177132687617369/100000000000000000000 : ℝ) := by
    have hpowers : (8773/50000 : ℝ)^4831 ≤ (27177132687617369/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8773 : ℕ)^4831*100000000000000000000^1024 ≤ 27177132687617369^1024*50000^4831 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8773 50000 27177132687617369 100000000000000000000 4831 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8773/50000 : ℝ)) (X := (27177132687617369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001466626072537119/50000000000000000000 : ℝ) ≤ (10000062173783531/10000000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (50001466626072537119/50000000000000000000 : ℝ)^1024 ≤ (10000062173783531/10000000000000000 : ℝ)^4831 := by
      have hnat : (50001466626072537119 : ℕ)^1024*10000000000000000^4831 ≤ 10000062173783531^4831*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001466626072537119 50000000000000000000 10000062173783531 10000000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000062173783531/10000000000000000 : ℝ)) (X := (50001466626072537119/50000000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503580469845019311/12500000000000000000 : ℝ) ≤ (10000607077192527/10000000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (12503580469845019311/12500000000000000000 : ℝ)^1024 ≤ (10000607077192527/10000000000000000 : ℝ)^4831 := by
      have hnat : (12503580469845019311 : ℕ)^1024*10000000000000000^4831 ≤ 10000607077192527^4831*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503580469845019311 12500000000000000000 10000607077192527 10000000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000607077192527/10000000000000000 : ℝ)) (X := (12503580469845019311/12500000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027177132687617369/50000000000000000000 : ℝ) ≤ (10001151980601523/10000000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (50027177132687617369/50000000000000000000 : ℝ)^1024 ≤ (10001151980601523/10000000000000000 : ℝ)^4831 := by
      have hnat : (50027177132687617369 : ℕ)^1024*10000000000000000^4831 ≤ 10001151980601523^4831*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027177132687617369 50000000000000000000 10001151980601523 10000000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001151980601523/10000000000000000 : ℝ)) (X := (50027177132687617369/50000000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1466626072537119/100000000000000000000 : ℝ) ≤ ((5059387792782590161/5060000000000000000 : ℝ)+2*(136225852249/202400000000000 : ℝ)*(189/2000 : ℝ))^(4831/1024 : ℝ) := by
    rw [show (5059387792782590161/5060000000000000000 : ℝ)+2*(136225852249/202400000000000 : ℝ)*(189/2000 : ℝ)=(10000062173783531/10000000000000000 : ℝ) by norm_num, show 1+2*(1466626072537119/100000000000000000000 : ℝ)=(50001466626072537119/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27177132687617369/100000000000000000000 : ℝ)+(1466626072537119/100000000000000000000 : ℝ) ≤ ((5059387792782590161/5060000000000000000 : ℝ)+(136225852249/202400000000000 : ℝ)*((8773/50000 : ℝ)+(189/2000 : ℝ)))^(4831/1024 : ℝ) := by
    rw [show (5059387792782590161/5060000000000000000 : ℝ)+(136225852249/202400000000000 : ℝ)*((8773/50000 : ℝ)+(189/2000 : ℝ))=(10000607077192527/10000000000000000 : ℝ) by norm_num, show 1+(27177132687617369/100000000000000000000 : ℝ)+(1466626072537119/100000000000000000000 : ℝ)=(12503580469845019311/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27177132687617369/100000000000000000000 : ℝ) ≤ ((5059387792782590161/5060000000000000000 : ℝ)+2*(136225852249/202400000000000 : ℝ)*(8773/50000 : ℝ))^(4831/1024 : ℝ) := by
    rw [show (5059387792782590161/5060000000000000000 : ℝ)+2*(136225852249/202400000000000 : ℝ)*(8773/50000 : ℝ)=(10001151980601523/10000000000000000 : ℝ) by norm_num, show 1+2*(27177132687617369/100000000000000000000 : ℝ)=(50027177132687617369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5059387792782590161/5060000000000000000 : ℝ)*(X 1 0+X 2 0)+(136225852249/202400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (189/2000 : ℝ)) (hi := (8773/50000 : ℝ)) (c := (5059387792782590161/5060000000000000000 : ℝ)) (alpha := (136225852249/202400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5059387792782590161/5060000000000000000 : ℝ)*(X 0 1+X 2 1)+(136225852249/202400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (189/2000 : ℝ)) (hi := (8773/50000 : ℝ)) (c := (5059387792782590161/5060000000000000000 : ℝ)) (alpha := (136225852249/202400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5059387792782590161/5060000000000000000 : ℝ)*(X 0 2+X 1 2)+(136225852249/202400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (189/2000 : ℝ)) (hi := (8773/50000 : ℝ)) (c := (5059387792782590161/5060000000000000000 : ℝ)) (alpha := (136225852249/202400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-414141189/2500000000 : ℝ)*X 0 0+(545892861/1000000000 : ℝ)*X 0 1+(5177925099/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214089481/400000000 : ℝ)*X 1 0+(-72059929/400000000 : ℝ)*X 1 1+(5177925147/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53522371/100000000 : ℝ)*X 2 0+(1035585001/2000000000 : ℝ)*X 2 1+(-900749157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4196455219/10000000000 : ℝ)*X 0 0+(240856517/625000000 : ℝ)*X 0 1+(4561532533/10000000000 : ℝ)*X 0 2+(4196455219/10000000000 : ℝ)*X 1 0+(240856517/625000000 : ℝ)*X 1 1+(4561532533/10000000000 : ℝ)*X 1 2+(4196455219/10000000000 : ℝ)*X 2 0+(240856517/625000000 : ℝ)*X 2 1+(4561532533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1656639209/10000000000 : ℝ)*X 0 0+(2590053379/5000000000 : ℝ)*X 0 1+(5456723429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319342221/2500000000 : ℝ)*X 1 0+(-1522699837/10000000000 : ℝ)*X 1 1+(682090443/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277369863/10000000000 : ℝ)*X 2 0+(85261287/156250000 : ℝ)*X 2 1+(-1522700127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1049160841/2500000000 : ℝ)*X 0 0+(284752423/625000000 : ℝ)*X 0 1+(3859258167/10000000000 : ℝ)*X 0 2+(1049160841/2500000000 : ℝ)*X 1 0+(284752423/625000000 : ℝ)*X 1 1+(3859258167/10000000000 : ℝ)*X 1 2+(1049160841/2500000000 : ℝ)*X 2 0+(284752423/625000000 : ℝ)*X 2 1+(3859258167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46900767475349921752209/5060000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1458083911/100000000000000 : ℝ)*(base19) + (696319109/50000000000000 : ℝ)*(base23) + (15429599/25000000000000 : ℝ)*(lower2) + (130149151/50000000000000 : ℝ)*(upper3) + (115099527/100000000000000 : ℝ)*(upper5) + (1242873965500129/50000000000000 : ℝ)*(major0) + (1242873965500129/50000000000000 : ℝ)*(major1) + (1242873965500129/50000000000000 : ℝ)*(major2) + (444836610024223/12500000000000 : ℝ)*(sp0) + (1779353958638041/50000000000000 : ℝ)*(sp1) + (222419248920111/6250000000000 : ℝ)*(sp2) + (1412778345836283/100000000000000 : ℝ)*(sp3) + (16495166209/100000000000000 : ℝ)*(sp4) + (3915920007/50000000000000 : ℝ)*(sp7) + (176598272209537/12500000000000 : ℝ)*(f.failure) + (1779354687679997/50000000000000 : ℝ)*(f.sum) + (22395121761159/5060000000000000000000000000 : ℝ)*base66 + (944603942732655769/253000000000000000000000000000000 : ℝ)*base67 + (561181233459344231/253000000000000000000000000000000 : ℝ)*base70 + (967133660283655769/253000000000000000000000000000000 : ℝ)*base71 + (30783066506559/5060000000000000000000000000 : ℝ)*base74 + (225358844040344231/253000000000000000000000000000000 : ℝ)*base76 + (363077987866344231/253000000000000000000000000000000 : ℝ)*base78 + (1320939363578655769/253000000000000000000000000000000 : ℝ)*base79 + (25008059335659/5060000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (17762741/1250000000000000000000 : ℝ)*base90 + (17762741/1250000000000000000000 : ℝ)*base92 + (17762741/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63706927764017580311812437/5500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1415672179/100000000000000 : ℝ)*(base19) + (2481560043/100000000000000 : ℝ)*(base23) + (307655447/100000000000000 : ℝ)*(upper3) + (40299087/25000000000000 : ℝ)*(lower4) + (1241759/50000000000000 : ℝ)*(upper5) + (2525139681855003/100000000000000 : ℝ)*(major0) + (2525139681855003/100000000000000 : ℝ)*(major1) + (2525139681855003/100000000000000 : ℝ)*(major2) + (42268139/312500000000 : ℝ)*(sp1) + (19856310531/100000000000000 : ℝ)*(sp2) + (723020863722011/20000000000000 : ℝ)*(sp4) + (903772344283349/25000000000000 : ℝ)*(sp5) + (3615081980739481/100000000000000 : ℝ)*(sp6) + (179396832374669/12500000000000 : ℝ)*(sp7) + (179396832374669/12500000000000 : ℝ)*(f.failure) + (723020863722011/20000000000000 : ℝ)*(f.sum) + (30847296045787/10120000000000000000000000000 : ℝ)*base65 + (395504619285899517/506000000000000000000000000000000 : ℝ)*base68 + (990602254096100483/506000000000000000000000000000000 : ℝ)*base69 + (1319076296718100483/506000000000000000000000000000000 : ℝ)*base71 + (19935999934333/10120000000000000000000000000 : ℝ)*base74 + (1119300627262100483/506000000000000000000000000000000 : ℝ)*base75 + (970928492384100483/506000000000000000000000000000000 : ℝ)*base77 + (1835506572376100483/506000000000000000000000000000000 : ℝ)*base79 + (1113832026187/10120000000000000000000000000 : ℝ)*base81 + (11668817/1250000000000000000000 : ℝ)*base90 + (11668817/1250000000000000000000 : ℝ)*base92 + (11668817/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1629_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8773/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (189/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5227/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16419/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1629_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1629_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5227/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16419/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1629_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1629_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1629_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5227/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16419/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1629_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
