-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1080_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:49:31.175869+00:00
-- url     : https://prove2.me/submissions/d6166014-0ddc-4f5a-b212-3f6d2062728f

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
theorem support_rectangle_w1080_s9_0 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336234971/2500000000 : ℝ)*x 0 + (-1131259601/5000000000 : ℝ)*x 1 + (5264732249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336234971/2500000000 : ℝ)^8273 ≤ (21747388420597/50000000000000 : ℝ)^6225 := by
    have hnat : (1336234971 : ℕ)^8273*50000000000000^6225 ≤ 21747388420597^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336234971 2500000000 21747388420597 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131259601/5000000000 : ℝ)^8273 ≤ (216808222967/1562500000000 : ℝ)^6225 := by
    have hnat : (1131259601 : ℕ)^8273*1562500000000^6225 ≤ 216808222967^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131259601 5000000000 216808222967 1562500000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264732249/10000000000 : ℝ)^8273 ≤ (42629496873583/100000000000000 : ℝ)^6225 := by
    have hnat : (5264732249 : ℕ)^8273*100000000000000^6225 ≤ 42629496873583^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264732249 10000000000 42629496873583 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336234971/2500000000 : ℝ), (-1131259601/5000000000 : ℝ), (5264732249/10000000000 : ℝ)] ![(21747388420597/50000000000000 : ℝ), (216808222967/1562500000000 : ℝ), (42629496873583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336234971/2500000000 : ℝ)|^8273 ≤ (21747388420597/50000000000000 : ℝ)^6225
        have hw : |(1336234971/2500000000 : ℝ)|=(1336234971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1131259601/5000000000 : ℝ)|^8273 ≤ (216808222967/1562500000000 : ℝ)^6225
        have hw : |(-1131259601/5000000000 : ℝ)|=(1131259601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264732249/10000000000 : ℝ)|^8273 ≤ (42629496873583/100000000000000 : ℝ)^6225
        have hw : |(5264732249/10000000000 : ℝ)|=(5264732249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s9_1 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2196897999/10000000000 : ℝ)*x 0 + (1316264151/2500000000 : ℝ)*x 1 + (5393761783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2196897999/10000000000 : ℝ)^8273 ≤ (13343445665287/100000000000000 : ℝ)^6225 := by
    have hnat : (2196897999 : ℕ)^8273*100000000000000^6225 ≤ 13343445665287^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196897999 10000000000 13343445665287 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316264151/2500000000 : ℝ)^8273 ≤ (5329123416617/12500000000000 : ℝ)^6225 := by
    have hnat : (1316264151 : ℕ)^8273*12500000000000^6225 ≤ 5329123416617^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316264151 2500000000 5329123416617 12500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393761783/10000000000 : ℝ)^8273 ≤ (44023566991543/100000000000000 : ℝ)^6225 := by
    have hnat : (5393761783 : ℕ)^8273*100000000000000^6225 ≤ 44023566991543^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393761783 10000000000 44023566991543 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2196897999/10000000000 : ℝ), (1316264151/2500000000 : ℝ), (5393761783/10000000000 : ℝ)] ![(13343445665287/100000000000000 : ℝ), (5329123416617/12500000000000 : ℝ), (44023566991543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2196897999/10000000000 : ℝ)|^8273 ≤ (13343445665287/100000000000000 : ℝ)^6225
        have hw : |(-2196897999/10000000000 : ℝ)|=(2196897999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316264151/2500000000 : ℝ)|^8273 ≤ (5329123416617/12500000000000 : ℝ)^6225
        have hw : |(1316264151/2500000000 : ℝ)|=(1316264151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393761783/10000000000 : ℝ)|^8273 ≤ (44023566991543/100000000000000 : ℝ)^6225
        have hw : |(5393761783/10000000000 : ℝ)|=(5393761783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s9_2 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312321817/10000000000 : ℝ)*x 0 + (-2133490031/10000000000 : ℝ)*x 1 + (1348440381/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312321817/10000000000 : ℝ)^8273 ≤ (1725694960651/4000000000000 : ℝ)^6225 := by
    have hnat : (5312321817 : ℕ)^8273*4000000000000^6225 ≤ 1725694960651^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312321817 10000000000 1725694960651 4000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2133490031/10000000000 : ℝ)^8273 ≤ (1283406178189/10000000000000 : ℝ)^6225 := by
    have hnat : (2133490031 : ℕ)^8273*10000000000000^6225 ≤ 1283406178189^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133490031 10000000000 1283406178189 10000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348440381/2500000000 : ℝ)^8273 ≤ (22011782091061/50000000000000 : ℝ)^6225 := by
    have hnat : (1348440381 : ℕ)^8273*50000000000000^6225 ≤ 22011782091061^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348440381 2500000000 22011782091061 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312321817/10000000000 : ℝ), (-2133490031/10000000000 : ℝ), (1348440381/2500000000 : ℝ)] ![(1725694960651/4000000000000 : ℝ), (1283406178189/10000000000000 : ℝ), (22011782091061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312321817/10000000000 : ℝ)|^8273 ≤ (1725694960651/4000000000000 : ℝ)^6225
        have hw : |(5312321817/10000000000 : ℝ)|=(5312321817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2133490031/10000000000 : ℝ)|^8273 ≤ (1283406178189/10000000000000 : ℝ)^6225
        have hw : |(-2133490031/10000000000 : ℝ)|=(2133490031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348440381/2500000000 : ℝ)|^8273 ≤ (22011782091061/50000000000000 : ℝ)^6225
        have hw : |(1348440381/2500000000 : ℝ)|=(1348440381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s9_3 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312321471/10000000000 : ℝ)*x 0 + (5393761899/10000000000 : ℝ)*x 1 + (-213348999/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312321471/10000000000 : ℝ)^8273 ≤ (43142370281887/100000000000000 : ℝ)^6225 := by
    have hnat : (5312321471 : ℕ)^8273*100000000000000^6225 ≤ 43142370281887^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312321471 10000000000 43142370281887 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393761899/10000000000 : ℝ)^8273 ≤ (44023568249817/100000000000000 : ℝ)^6225 := by
    have hnat : (5393761899 : ℕ)^8273*100000000000000^6225 ≤ 44023568249817^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393761899 10000000000 44023568249817 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213348999/1000000000 : ℝ)^8273 ≤ (12834061454111/100000000000000 : ℝ)^6225 := by
    have hnat : (213348999 : ℕ)^8273*100000000000000^6225 ≤ 12834061454111^6225*1000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213348999 1000000000 12834061454111 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312321471/10000000000 : ℝ), (5393761899/10000000000 : ℝ), (-213348999/1000000000 : ℝ)] ![(43142370281887/100000000000000 : ℝ), (44023568249817/100000000000000 : ℝ), (12834061454111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312321471/10000000000 : ℝ)|^8273 ≤ (43142370281887/100000000000000 : ℝ)^6225
        have hw : |(5312321471/10000000000 : ℝ)|=(5312321471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393761899/10000000000 : ℝ)|^8273 ≤ (44023568249817/100000000000000 : ℝ)^6225
        have hw : |(5393761899/10000000000 : ℝ)|=(5393761899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-213348999/1000000000 : ℝ)|^8273 ≤ (12834061454111/100000000000000 : ℝ)^6225
        have hw : |(-213348999/1000000000 : ℝ)|=(213348999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s9_4 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186746979/5000000000 : ℝ)*x 0 + (225091139/500000000 : ℝ)*x 1 + (424887747/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186746979/5000000000 : ℝ)^8273 ≤ (266533957031/800000000000 : ℝ)^6225 := by
    have hnat : (2186746979 : ℕ)^8273*800000000000^6225 ≤ 266533957031^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186746979 5000000000 266533957031 800000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225091139/500000000 : ℝ)^8273 ≤ (34622192619569/100000000000000 : ℝ)^6225 := by
    have hnat : (225091139 : ℕ)^8273*100000000000000^6225 ≤ 34622192619569^6225*500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225091139 500000000 34622192619569 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424887747/1000000000 : ℝ)^8273 ≤ (3206106273967/10000000000000 : ℝ)^6225 := by
    have hnat : (424887747 : ℕ)^8273*10000000000000^6225 ≤ 3206106273967^6225*1000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424887747 1000000000 3206106273967 10000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186746979/5000000000 : ℝ), (225091139/500000000 : ℝ), (424887747/1000000000 : ℝ)] ![(266533957031/800000000000 : ℝ), (34622192619569/100000000000000 : ℝ), (3206106273967/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186746979/5000000000 : ℝ)|^8273 ≤ (266533957031/800000000000 : ℝ)^6225
        have hw : |(2186746979/5000000000 : ℝ)|=(2186746979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225091139/500000000 : ℝ)|^8273 ≤ (34622192619569/100000000000000 : ℝ)^6225
        have hw : |(225091139/500000000 : ℝ)|=(225091139/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424887747/1000000000 : ℝ)|^8273 ≤ (3206106273967/10000000000000 : ℝ)^6225
        have hw : |(424887747/1000000000 : ℝ)|=(424887747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1080_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11271/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14011/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3503/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11271/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3503/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11271/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3503/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11271/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3503/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11271/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3503/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11271/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3503/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11271/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11271/100000 : ℝ) ^ (517/128 : ℝ) ≤ (14818938044565629/100000000000000000000 : ℝ) := by
    have hpowers : (11271/100000 : ℝ)^517 ≤ (14818938044565629/100000000000000000000 : ℝ)^128 := by
      have hnat : (11271 : ℕ)^517*100000000000000000000^128 ≤ 14818938044565629^128*100000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11271 100000 14818938044565629 100000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11271/100000 : ℝ)) (X := (14818938044565629/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hpowhi : (3503/25000 : ℝ) ^ (517/128 : ℝ) ≤ (35699380179222133/100000000000000000000 : ℝ) := by
    have hpowers : (3503/25000 : ℝ)^517 ≤ (35699380179222133/100000000000000000000 : ℝ)^128 := by
      have hnat : (3503 : ℕ)^517*100000000000000000000^128 ≤ 35699380179222133^128*25000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3503 25000 35699380179222133 100000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3503/25000 : ℝ)) (X := (35699380179222133/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014818938044565629/50000000000000000000 : ℝ) ≤ (2000146739853757/2000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (50014818938044565629/50000000000000000000 : ℝ)^128 ≤ (2000146739853757/2000000000000000 : ℝ)^517 := by
      have hnat : (50014818938044565629 : ℕ)^128*2000000000000000^517 ≤ 2000146739853757^517*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014818938044565629 50000000000000000000 2000146739853757 2000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000146739853757/2000000000000000 : ℝ)) (X := (50014818938044565629/50000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025259159111893881/50000000000000000000 : ℝ) ≤ (5000625253011399/5000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (50025259159111893881/50000000000000000000 : ℝ)^128 ≤ (5000625253011399/5000000000000000 : ℝ)^517 := by
      have hnat : (50025259159111893881 : ℕ)^128*5000000000000000^517 ≤ 5000625253011399^517*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025259159111893881 50000000000000000000 5000625253011399 5000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000625253011399/5000000000000000 : ℝ)) (X := (50025259159111893881/50000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035699380179222133/50000000000000000000 : ℝ) ≤ (10001767312776811/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (50035699380179222133/50000000000000000000 : ℝ)^128 ≤ (10001767312776811/10000000000000000 : ℝ)^517 := by
      have hnat : (50035699380179222133 : ℕ)^128*10000000000000000^517 ≤ 10001767312776811^517*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035699380179222133 50000000000000000000 10001767312776811 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001767312776811/10000000000000000 : ℝ)) (X := (50035699380179222133/50000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14818938044565629/100000000000000000000 : ℝ) ≤ ((27400361211846778639/27410000000000000000 : ℝ)+2*(516806754013/274100000000000 : ℝ)*(11271/100000 : ℝ))^(517/128 : ℝ) := by
    rw [show (27400361211846778639/27410000000000000000 : ℝ)+2*(516806754013/274100000000000 : ℝ)*(11271/100000 : ℝ)=(2000146739853757/2000000000000000 : ℝ) by norm_num, show 1+2*(14818938044565629/100000000000000000000 : ℝ)=(50014818938044565629/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35699380179222133/100000000000000000000 : ℝ)+(14818938044565629/100000000000000000000 : ℝ) ≤ ((27400361211846778639/27410000000000000000 : ℝ)+(516806754013/274100000000000 : ℝ)*((3503/25000 : ℝ)+(11271/100000 : ℝ)))^(517/128 : ℝ) := by
    rw [show (27400361211846778639/27410000000000000000 : ℝ)+(516806754013/274100000000000 : ℝ)*((3503/25000 : ℝ)+(11271/100000 : ℝ))=(5000625253011399/5000000000000000 : ℝ) by norm_num, show 1+(35699380179222133/100000000000000000000 : ℝ)+(14818938044565629/100000000000000000000 : ℝ)=(50025259159111893881/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35699380179222133/100000000000000000000 : ℝ) ≤ ((27400361211846778639/27410000000000000000 : ℝ)+2*(516806754013/274100000000000 : ℝ)*(3503/25000 : ℝ))^(517/128 : ℝ) := by
    rw [show (27400361211846778639/27410000000000000000 : ℝ)+2*(516806754013/274100000000000 : ℝ)*(3503/25000 : ℝ)=(10001767312776811/10000000000000000 : ℝ) by norm_num, show 1+2*(35699380179222133/100000000000000000000 : ℝ)=(50035699380179222133/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27400361211846778639/27410000000000000000 : ℝ)*(X 1 0+X 2 0)+(516806754013/274100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (11271/100000 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (27400361211846778639/27410000000000000000 : ℝ)) (alpha := (516806754013/274100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27400361211846778639/27410000000000000000 : ℝ)*(X 0 1+X 2 1)+(516806754013/274100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (11271/100000 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (27400361211846778639/27410000000000000000 : ℝ)) (alpha := (516806754013/274100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27400361211846778639/27410000000000000000 : ℝ)*(X 0 2+X 1 2)+(516806754013/274100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (11271/100000 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (27400361211846778639/27410000000000000000 : ℝ)) (alpha := (516806754013/274100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1336234971/2500000000 : ℝ)*X 1 0+(-1131259601/5000000000 : ℝ)*X 1 1+(5264732249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s9_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2196897999/10000000000 : ℝ)*X 0 0+(1316264151/2500000000 : ℝ)*X 0 1+(5393761783/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5312321817/10000000000 : ℝ)*X 1 0+(-2133490031/10000000000 : ℝ)*X 1 1+(1348440381/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312321471/10000000000 : ℝ)*X 2 0+(5393761899/10000000000 : ℝ)*X 2 1+(-213348999/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2186746979/5000000000 : ℝ)*X 0 0+(225091139/500000000 : ℝ)*X 0 1+(424887747/1000000000 : ℝ)*X 0 2+(2186746979/5000000000 : ℝ)*X 1 0+(225091139/500000000 : ℝ)*X 1 1+(424887747/1000000000 : ℝ)*X 1 2+(2186746979/5000000000 : ℝ)*X 2 0+(225091139/500000000 : ℝ)*X 2 1+(424887747/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1083977090125437700875472377/274100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67392711/5000000000000 : ℝ)*(base19) + (472117091/50000000000000 : ℝ)*(base23) + (76918109/25000000000000 : ℝ)*(lower1) + (841573/781250000000 : ℝ)*(upper3) + (55482731/100000000000000 : ℝ)*(lower4) + (10612993/6250000000000 : ℝ)*(upper5) + (1172307480988127/20000000000000 : ℝ)*(major0) + (1172307480988127/20000000000000 : ℝ)*(major1) + (1172307480988127/20000000000000 : ℝ)*(major2) + (327493811/100000000000000 : ℝ)*(sp0) + (3884833754164569/50000000000000 : ℝ)*(sp1) + (7769665832981107/100000000000000 : ℝ)*(sp2) + (1942416641023739/25000000000000 : ℝ)*(sp3) + (1976703584864773/50000000000000 : ℝ)*(sp4) + (1976703584864773/50000000000000 : ℝ)*(f.failure) + (3884833754164569/50000000000000 : ℝ)*(f.sum) + (2072310913799/548200000000000000000000000 : ℝ)*base66 + (1396428322261080847/548200000000000000000000000000000 : ℝ)*base68 + (3438679687765480847/548200000000000000000000000000000 : ℝ)*base70 + (4214761349788880847/548200000000000000000000000000000 : ℝ)*base72 + (236569174143/274100000000000000000000000 : ℝ)*base74 + (448470683000080847/548200000000000000000000000000000 : ℝ)*base76 + (2789239027259480847/548200000000000000000000000000000 : ℝ)*base78 + (2524818035495480847/548200000000000000000000000000000 : ℝ)*base80 + (13929872752271/2741000000000000000000000000 : ℝ)*base81 + (13185063/2500000000000000000000 : ℝ)*base89 + (13185063/2500000000000000000000 : ℝ)*base91 + (13185063/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1080_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11271/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1080_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1080_box_0 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1033958061/5000000000 : ℝ)*x 0 + (5377176671/10000000000 : ℝ)*x 1 + (33607351/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033958061/5000000000 : ℝ)^8273 ≤ (12312493049529/100000000000000 : ℝ)^6225 := by
    have hnat : (1033958061 : ℕ)^8273*100000000000000^6225 ≤ 12312493049529^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033958061 5000000000 12312493049529 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377176671/10000000000 : ℝ)^8273 ≤ (43843756235841/100000000000000 : ℝ)^6225 := by
    have hnat : (5377176671 : ℕ)^8273*100000000000000^6225 ≤ 43843756235841^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377176671 10000000000 43843756235841 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33607351/62500000 : ℝ)^8273 ≤ (21921875349271/50000000000000 : ℝ)^6225 := by
    have hnat : (33607351 : ℕ)^8273*50000000000000^6225 ≤ 21921875349271^6225*62500000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33607351 62500000 21921875349271 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1033958061/5000000000 : ℝ), (5377176671/10000000000 : ℝ), (33607351/62500000 : ℝ)] ![(12312493049529/100000000000000 : ℝ), (43843756235841/100000000000000 : ℝ), (21921875349271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1033958061/5000000000 : ℝ)|^8273 ≤ (12312493049529/100000000000000 : ℝ)^6225
        have hw : |(-1033958061/5000000000 : ℝ)|=(1033958061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377176671/10000000000 : ℝ)|^8273 ≤ (43843756235841/100000000000000 : ℝ)^6225
        have hw : |(5377176671/10000000000 : ℝ)|=(5377176671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33607351/62500000 : ℝ)|^8273 ≤ (21921875349271/50000000000000 : ℝ)^6225
        have hw : |(33607351/62500000 : ℝ)|=(33607351/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_1 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647679/5000000 : ℝ)*x 0 + (-544678589/2500000000 : ℝ)*x 1 + (672147051/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647679/5000000 : ℝ)^8273 ≤ (42959379297411/100000000000000 : ℝ)^6225 := by
    have hnat : (2647679 : ℕ)^8273*100000000000000^6225 ≤ 42959379297411^6225*5000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647679 5000000 42959379297411 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544678589/2500000000 : ℝ)^8273 ≤ (824804206771/6250000000000 : ℝ)^6225 := by
    have hnat : (544678589 : ℕ)^8273*6250000000000^6225 ≤ 824804206771^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544678589 2500000000 824804206771 6250000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672147051/1250000000 : ℝ)^8273 ≤ (137011729331/312500000000 : ℝ)^6225 := by
    have hnat : (672147051 : ℕ)^8273*312500000000^6225 ≤ 137011729331^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672147051 1250000000 137011729331 312500000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647679/5000000 : ℝ), (-544678589/2500000000 : ℝ), (672147051/1250000000 : ℝ)] ![(42959379297411/100000000000000 : ℝ), (824804206771/6250000000000 : ℝ), (137011729331/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647679/5000000 : ℝ)|^8273 ≤ (42959379297411/100000000000000 : ℝ)^6225
        have hw : |(2647679/5000000 : ℝ)|=(2647679/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544678589/2500000000 : ℝ)|^8273 ≤ (824804206771/6250000000000 : ℝ)^6225
        have hw : |(-544678589/2500000000 : ℝ)|=(544678589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672147051/1250000000 : ℝ)|^8273 ≤ (137011729331/312500000000 : ℝ)^6225
        have hw : |(672147051/1250000000 : ℝ)|=(672147051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_2 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647678993/5000000000 : ℝ)*x 0 + (2688588201/5000000000 : ℝ)*x 1 + (-2178714383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647678993/5000000000 : ℝ)^8273 ≤ (10739844786617/25000000000000 : ℝ)^6225 := by
    have hnat : (2647678993 : ℕ)^8273*25000000000000^6225 ≤ 10739844786617^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647678993 5000000000 10739844786617 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688588201/5000000000 : ℝ)^8273 ≤ (43843753320903/100000000000000 : ℝ)^6225 := by
    have hnat : (2688588201 : ℕ)^8273*100000000000000^6225 ≤ 43843753320903^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688588201 5000000000 43843753320903 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2178714383/10000000000 : ℝ)^8273 ≤ (2639373505137/20000000000000 : ℝ)^6225 := by
    have hnat : (2178714383 : ℕ)^8273*20000000000000^6225 ≤ 2639373505137^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178714383 10000000000 2639373505137 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647678993/5000000000 : ℝ), (2688588201/5000000000 : ℝ), (-2178714383/10000000000 : ℝ)] ![(10739844786617/25000000000000 : ℝ), (43843753320903/100000000000000 : ℝ), (2639373505137/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647678993/5000000000 : ℝ)|^8273 ≤ (10739844786617/25000000000000 : ℝ)^6225
        have hw : |(2647678993/5000000000 : ℝ)|=(2647678993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688588201/5000000000 : ℝ)|^8273 ≤ (43843753320903/100000000000000 : ℝ)^6225
        have hw : |(2688588201/5000000000 : ℝ)|=(2688588201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2178714383/10000000000 : ℝ)|^8273 ≤ (2639373505137/20000000000000 : ℝ)^6225
        have hw : |(-2178714383/10000000000 : ℝ)|=(2178714383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_3 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (280106977/625000000 : ℝ)*x 0 + (4321522287/10000000000 : ℝ)*x 1 + (4321521747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280106977/625000000 : ℝ)^8273 ≤ (34416789460633/100000000000000 : ℝ)^6225 := by
    have hnat : (280106977 : ℕ)^8273*100000000000000^6225 ≤ 34416789460633^6225*625000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280106977 625000000 34416789460633 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4321522287/10000000000 : ℝ)^8273 ≤ (8197901996531/25000000000000 : ℝ)^6225 := by
    have hnat : (4321522287 : ℕ)^8273*25000000000000^6225 ≤ 8197901996531^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321522287 10000000000 8197901996531 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4321521747/10000000000 : ℝ)^8273 ≤ (16395801270277/50000000000000 : ℝ)^6225 := by
    have hnat : (4321521747 : ℕ)^8273*50000000000000^6225 ≤ 16395801270277^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321521747 10000000000 16395801270277 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(280106977/625000000 : ℝ), (4321522287/10000000000 : ℝ), (4321521747/10000000000 : ℝ)] ![(34416789460633/100000000000000 : ℝ), (8197901996531/25000000000000 : ℝ), (16395801270277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(280106977/625000000 : ℝ)|^8273 ≤ (34416789460633/100000000000000 : ℝ)^6225
        have hw : |(280106977/625000000 : ℝ)|=(280106977/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4321522287/10000000000 : ℝ)|^8273 ≤ (8197901996531/25000000000000 : ℝ)^6225
        have hw : |(4321522287/10000000000 : ℝ)|=(4321522287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4321521747/10000000000 : ℝ)|^8273 ≤ (16395801270277/50000000000000 : ℝ)^6225
        have hw : |(4321521747/10000000000 : ℝ)|=(4321521747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_4 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1163631323/5000000000 : ℝ)*x 0 + (1320073801/2500000000 : ℝ)*x 1 + (5280295601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1163631323/5000000000 : ℝ)^8273 ≤ (3601472364089/25000000000000 : ℝ)^6225 := by
    have hnat : (1163631323 : ℕ)^8273*25000000000000^6225 ≤ 3601472364089^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163631323 5000000000 3601472364089 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320073801/2500000000 : ℝ)^8273 ≤ (42797053127197/100000000000000 : ℝ)^6225 := by
    have hnat : (1320073801 : ℕ)^8273*100000000000000^6225 ≤ 42797053127197^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320073801 2500000000 42797053127197 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280295601/10000000000 : ℝ)^8273 ≤ (21398528701757/50000000000000 : ℝ)^6225 := by
    have hnat : (5280295601 : ℕ)^8273*50000000000000^6225 ≤ 21398528701757^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280295601 10000000000 21398528701757 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1163631323/5000000000 : ℝ), (1320073801/2500000000 : ℝ), (5280295601/10000000000 : ℝ)] ![(3601472364089/25000000000000 : ℝ), (42797053127197/100000000000000 : ℝ), (21398528701757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1163631323/5000000000 : ℝ)|^8273 ≤ (3601472364089/25000000000000 : ℝ)^6225
        have hw : |(-1163631323/5000000000 : ℝ)|=(1163631323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320073801/2500000000 : ℝ)|^8273 ≤ (42797053127197/100000000000000 : ℝ)^6225
        have hw : |(1320073801/2500000000 : ℝ)|=(1320073801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280295601/10000000000 : ℝ)|^8273 ≤ (21398528701757/50000000000000 : ℝ)^6225
        have hw : |(5280295601/10000000000 : ℝ)|=(5280295601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_5 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536390031/1000000000 : ℝ)*x 0 + (-2216634493/10000000000 : ℝ)*x 1 + (660036943/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536390031/1000000000 : ℝ)^8273 ≤ (2184997468049/5000000000000 : ℝ)^6225 := by
    have hnat : (536390031 : ℕ)^8273*5000000000000^6225 ≤ 2184997468049^6225*1000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536390031 1000000000 2184997468049 5000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216634493/10000000000 : ℝ)^8273 ≤ (2700598766881/20000000000000 : ℝ)^6225 := by
    have hnat : (2216634493 : ℕ)^8273*20000000000000^6225 ≤ 2700598766881^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216634493 10000000000 2700598766881 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660036943/1250000000 : ℝ)^8273 ≤ (21398528394767/50000000000000 : ℝ)^6225 := by
    have hnat : (660036943 : ℕ)^8273*50000000000000^6225 ≤ 21398528394767^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660036943 1250000000 21398528394767 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536390031/1000000000 : ℝ), (-2216634493/10000000000 : ℝ), (660036943/1250000000 : ℝ)] ![(2184997468049/5000000000000 : ℝ), (2700598766881/20000000000000 : ℝ), (21398528394767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536390031/1000000000 : ℝ)|^8273 ≤ (2184997468049/5000000000000 : ℝ)^6225
        have hw : |(536390031/1000000000 : ℝ)|=(536390031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2216634493/10000000000 : ℝ)|^8273 ≤ (2700598766881/20000000000000 : ℝ)^6225
        have hw : |(-2216634493/10000000000 : ℝ)|=(2216634493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660036943/1250000000 : ℝ)|^8273 ≤ (21398528394767/50000000000000 : ℝ)^6225
        have hw : |(660036943/1250000000 : ℝ)|=(660036943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_6 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1340975117/2500000000 : ℝ)*x 0 + (660036969/1250000000 : ℝ)*x 1 + (-443326801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340975117/2500000000 : ℝ)^8273 ≤ (10924987767927/25000000000000 : ℝ)^6225 := by
    have hnat : (1340975117 : ℕ)^8273*25000000000000^6225 ≤ 10924987767927^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340975117 2500000000 10924987767927 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660036969/1250000000 : ℝ)^8273 ≤ (21398529515011/50000000000000 : ℝ)^6225 := by
    have hnat : (660036969 : ℕ)^8273*50000000000000^6225 ≤ 21398529515011^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660036969 1250000000 21398529515011 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443326801/2000000000 : ℝ)^8273 ≤ (1687873735457/12500000000000 : ℝ)^6225 := by
    have hnat : (443326801 : ℕ)^8273*12500000000000^6225 ≤ 1687873735457^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443326801 2000000000 1687873735457 12500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340975117/2500000000 : ℝ), (660036969/1250000000 : ℝ), (-443326801/2000000000 : ℝ)] ![(10924987767927/25000000000000 : ℝ), (21398529515011/50000000000000 : ℝ), (1687873735457/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340975117/2500000000 : ℝ)|^8273 ≤ (10924987767927/25000000000000 : ℝ)^6225
        have hw : |(1340975117/2500000000 : ℝ)|=(1340975117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660036969/1250000000 : ℝ)|^8273 ≤ (21398529515011/50000000000000 : ℝ)^6225
        have hw : |(660036969/1250000000 : ℝ)|=(660036969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-443326801/2000000000 : ℝ)|^8273 ≤ (1687873735457/12500000000000 : ℝ)^6225
        have hw : |(-443326801/2000000000 : ℝ)|=(443326801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_7 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2132460691/5000000000 : ℝ)*x 0 + (2214948061/5000000000 : ℝ)*x 1 + (2214947741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132460691/5000000000 : ℝ)^8273 ≤ (32222055778431/100000000000000 : ℝ)^6225 := by
    have hnat : (2132460691 : ℕ)^8273*100000000000000^6225 ≤ 32222055778431^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132460691 5000000000 32222055778431 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2214948061/5000000000 : ℝ)^8273 ≤ (4236121919519/12500000000000 : ℝ)^6225 := by
    have hnat : (2214948061 : ℕ)^8273*12500000000000^6225 ≤ 4236121919519^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214948061 5000000000 4236121919519 12500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214947741/5000000000 : ℝ)^8273 ≤ (4236121106167/12500000000000 : ℝ)^6225 := by
    have hnat : (2214947741 : ℕ)^8273*12500000000000^6225 ≤ 4236121106167^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214947741 5000000000 4236121106167 12500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2132460691/5000000000 : ℝ), (2214948061/5000000000 : ℝ), (2214947741/5000000000 : ℝ)] ![(32222055778431/100000000000000 : ℝ), (4236121919519/12500000000000 : ℝ), (4236121106167/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2132460691/5000000000 : ℝ)|^8273 ≤ (32222055778431/100000000000000 : ℝ)^6225
        have hw : |(2132460691/5000000000 : ℝ)|=(2132460691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2214948061/5000000000 : ℝ)|^8273 ≤ (4236121919519/12500000000000 : ℝ)^6225
        have hw : |(2214948061/5000000000 : ℝ)|=(2214948061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2214947741/5000000000 : ℝ)|^8273 ≤ (4236121106167/12500000000000 : ℝ)^6225
        have hw : |(2214947741/5000000000 : ℝ)|=(2214947741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_8 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2273104107/10000000000 : ℝ)*x 0 + (5214528577/10000000000 : ℝ)*x 1 + (5386778697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2273104107/10000000000 : ℝ)^8273 ≤ (13962065432337/100000000000000 : ℝ)^6225 := by
    have hnat : (2273104107 : ℕ)^8273*100000000000000^6225 ≤ 13962065432337^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273104107 10000000000 13962065432337 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214528577/10000000000 : ℝ)^8273 ≤ (10522524564367/25000000000000 : ℝ)^6225 := by
    have hnat : (5214528577 : ℕ)^8273*25000000000000^6225 ≤ 10522524564367^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214528577 10000000000 10522524564367 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386778697/10000000000 : ℝ)^8273 ≤ (43947836286919/100000000000000 : ℝ)^6225 := by
    have hnat : (5386778697 : ℕ)^8273*100000000000000^6225 ≤ 43947836286919^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386778697 10000000000 43947836286919 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2273104107/10000000000 : ℝ), (5214528577/10000000000 : ℝ), (5386778697/10000000000 : ℝ)] ![(13962065432337/100000000000000 : ℝ), (10522524564367/25000000000000 : ℝ), (43947836286919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2273104107/10000000000 : ℝ)|^8273 ≤ (13962065432337/100000000000000 : ℝ)^6225
        have hw : |(-2273104107/10000000000 : ℝ)|=(2273104107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214528577/10000000000 : ℝ)|^8273 ≤ (10522524564367/25000000000000 : ℝ)^6225
        have hw : |(5214528577/10000000000 : ℝ)|=(5214528577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386778697/10000000000 : ℝ)|^8273 ≤ (43947836286919/100000000000000 : ℝ)^6225
        have hw : |(5386778697/10000000000 : ℝ)|=(5386778697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_9 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644280353/5000000000 : ℝ)*x 0 + (-67965151/312500000 : ℝ)*x 1 + (1077355859/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644280353/5000000000 : ℝ)^8273 ≤ (10721527136093/25000000000000 : ℝ)^6225 := by
    have hnat : (2644280353 : ℕ)^8273*25000000000000^6225 ≤ 10721527136093^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644280353 5000000000 10721527136093 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67965151/312500000 : ℝ)^8273 ≤ (13166048674669/100000000000000 : ℝ)^6225 := by
    have hnat : (67965151 : ℕ)^8273*100000000000000^6225 ≤ 13166048674669^6225*312500000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67965151 312500000 13166048674669 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077355859/2000000000 : ℝ)^8273 ≤ (43947842770773/100000000000000 : ℝ)^6225 := by
    have hnat : (1077355859 : ℕ)^8273*100000000000000^6225 ≤ 43947842770773^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077355859 2000000000 43947842770773 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644280353/5000000000 : ℝ), (-67965151/312500000 : ℝ), (1077355859/2000000000 : ℝ)] ![(10721527136093/25000000000000 : ℝ), (13166048674669/100000000000000 : ℝ), (43947842770773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644280353/5000000000 : ℝ)|^8273 ≤ (10721527136093/25000000000000 : ℝ)^6225
        have hw : |(2644280353/5000000000 : ℝ)|=(2644280353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67965151/312500000 : ℝ)|^8273 ≤ (13166048674669/100000000000000 : ℝ)^6225
        have hw : |(-67965151/312500000 : ℝ)|=(67965151/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077355859/2000000000 : ℝ)|^8273 ≤ (43947842770773/100000000000000 : ℝ)^6225
        have hw : |(1077355859/2000000000 : ℝ)|=(1077355859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_10 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322140171/2500000000 : ℝ)*x 0 + (5386778613/10000000000 : ℝ)*x 1 + (-2174885781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322140171/2500000000 : ℝ)^8273 ≤ (1715444332291/4000000000000 : ℝ)^6225 := by
    have hnat : (1322140171 : ℕ)^8273*4000000000000^6225 ≤ 1715444332291^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322140171 2500000000 1715444332291 4000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386778613/10000000000 : ℝ)^8273 ≤ (43947835376143/100000000000000 : ℝ)^6225 := by
    have hnat : (5386778613 : ℕ)^8273*100000000000000^6225 ≤ 43947835376143^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386778613 10000000000 43947835376143 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2174885781/10000000000 : ℝ)^8273 ≤ (1316605630967/10000000000000 : ℝ)^6225 := by
    have hnat : (2174885781 : ℕ)^8273*10000000000000^6225 ≤ 1316605630967^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174885781 10000000000 1316605630967 10000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322140171/2500000000 : ℝ), (5386778613/10000000000 : ℝ), (-2174885781/10000000000 : ℝ)] ![(1715444332291/4000000000000 : ℝ), (43947835376143/100000000000000 : ℝ), (1316605630967/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322140171/2500000000 : ℝ)|^8273 ≤ (1715444332291/4000000000000 : ℝ)^6225
        have hw : |(1322140171/2500000000 : ℝ)|=(1322140171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386778613/10000000000 : ℝ)|^8273 ≤ (43947835376143/100000000000000 : ℝ)^6225
        have hw : |(5386778613/10000000000 : ℝ)|=(5386778613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2174885781/10000000000 : ℝ)|^8273 ≤ (1316605630967/10000000000000 : ℝ)^6225
        have hw : |(-2174885781/10000000000 : ℝ)|=(2174885781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_11 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2251463009/5000000000 : ℝ)*x 0 + (4310774273/10000000000 : ℝ)*x 1 + (862154863/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2251463009/5000000000 : ℝ)^8273 ≤ (8658367294411/25000000000000 : ℝ)^6225 := by
    have hnat : (2251463009 : ℕ)^8273*25000000000000^6225 ≤ 8658367294411^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251463009 5000000000 8658367294411 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4310774273/10000000000 : ℝ)^8273 ≤ (16341632595719/50000000000000 : ℝ)^6225 := by
    have hnat : (4310774273 : ℕ)^8273*50000000000000^6225 ≤ 16341632595719^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310774273 10000000000 16341632595719 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (862154863/2000000000 : ℝ)^8273 ≤ (8170816403659/25000000000000 : ℝ)^6225 := by
    have hnat : (862154863 : ℕ)^8273*25000000000000^6225 ≤ 8170816403659^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862154863 2000000000 8170816403659 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2251463009/5000000000 : ℝ), (4310774273/10000000000 : ℝ), (862154863/2000000000 : ℝ)] ![(8658367294411/25000000000000 : ℝ), (16341632595719/50000000000000 : ℝ), (8170816403659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2251463009/5000000000 : ℝ)|^8273 ≤ (8658367294411/25000000000000 : ℝ)^6225
        have hw : |(2251463009/5000000000 : ℝ)|=(2251463009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4310774273/10000000000 : ℝ)|^8273 ≤ (16341632595719/50000000000000 : ℝ)^6225
        have hw : |(4310774273/10000000000 : ℝ)|=(4310774273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(862154863/2000000000 : ℝ)|^8273 ≤ (8170816403659/25000000000000 : ℝ)^6225
        have hw : |(862154863/2000000000 : ℝ)|=(862154863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_12 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-84897347/400000000 : ℝ)*x 0 + (217664759/400000000 : ℝ)*x 1 + (5272287117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84897347/400000000 : ℝ)^8273 ≤ (1274574598817/10000000000000 : ℝ)^6225 := by
    have hnat : (84897347 : ℕ)^8273*10000000000000^6225 ≤ 1274574598817^6225*400000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84897347 400000000 1274574598817 10000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217664759/400000000 : ℝ)^8273 ≤ (44543439084119/100000000000000 : ℝ)^6225 := by
    have hnat : (217664759 : ℕ)^8273*100000000000000^6225 ≤ 44543439084119^6225*400000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217664759 400000000 44543439084119 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272287117/10000000000 : ℝ)^8273 ≤ (21355407460243/50000000000000 : ℝ)^6225 := by
    have hnat : (5272287117 : ℕ)^8273*50000000000000^6225 ≤ 21355407460243^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272287117 10000000000 21355407460243 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84897347/400000000 : ℝ), (217664759/400000000 : ℝ), (5272287117/10000000000 : ℝ)] ![(1274574598817/10000000000000 : ℝ), (44543439084119/100000000000000 : ℝ), (21355407460243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84897347/400000000 : ℝ)|^8273 ≤ (1274574598817/10000000000000 : ℝ)^6225
        have hw : |(-84897347/400000000 : ℝ)|=(84897347/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217664759/400000000 : ℝ)|^8273 ≤ (44543439084119/100000000000000 : ℝ)^6225
        have hw : |(217664759/400000000 : ℝ)|=(217664759/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272287117/10000000000 : ℝ)|^8273 ≤ (21355407460243/50000000000000 : ℝ)^6225
        have hw : |(5272287117/10000000000 : ℝ)|=(5272287117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_13 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53695641/100000000 : ℝ)*x 0 + (-2219710713/10000000000 : ℝ)*x 1 + (5272286839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53695641/100000000 : ℝ)^8273 ≤ (5470160511363/12500000000000 : ℝ)^6225 := by
    have hnat : (53695641 : ℕ)^8273*12500000000000^6225 ≤ 5470160511363^6225*100000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53695641 100000000 5470160511363 12500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2219710713/10000000000 : ℝ)^8273 ≤ (2705580794609/20000000000000 : ℝ)^6225 := by
    have hnat : (2219710713 : ℕ)^8273*20000000000000^6225 ≤ 2705580794609^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219710713 10000000000 2705580794609 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272286839/10000000000 : ℝ)^8273 ≤ (21355405963741/50000000000000 : ℝ)^6225 := by
    have hnat : (5272286839 : ℕ)^8273*50000000000000^6225 ≤ 21355405963741^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272286839 10000000000 21355405963741 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53695641/100000000 : ℝ), (-2219710713/10000000000 : ℝ), (5272286839/10000000000 : ℝ)] ![(5470160511363/12500000000000 : ℝ), (2705580794609/20000000000000 : ℝ), (21355405963741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53695641/100000000 : ℝ)|^8273 ≤ (5470160511363/12500000000000 : ℝ)^6225
        have hw : |(53695641/100000000 : ℝ)|=(53695641/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2219710713/10000000000 : ℝ)|^8273 ≤ (2705580794609/20000000000000 : ℝ)^6225
        have hw : |(-2219710713/10000000000 : ℝ)|=(2219710713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272286839/10000000000 : ℝ)|^8273 ≤ (21355405963741/50000000000000 : ℝ)^6225
        have hw : |(5272286839/10000000000 : ℝ)|=(5272286839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_14 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369563913/10000000000 : ℝ)*x 0 + (5272287151/10000000000 : ℝ)*x 1 + (-554927637/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369563913/10000000000 : ℝ)^8273 ≤ (21880641032739/50000000000000 : ℝ)^6225 := by
    have hnat : (5369563913 : ℕ)^8273*50000000000000^6225 ≤ 21880641032739^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369563913 10000000000 21880641032739 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272287151/10000000000 : ℝ)^8273 ≤ (42710815286537/100000000000000 : ℝ)^6225 := by
    have hnat : (5272287151 : ℕ)^8273*100000000000000^6225 ≤ 42710815286537^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272287151 10000000000 42710815286537 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554927637/2500000000 : ℝ)^8273 ≤ (3381975659157/25000000000000 : ℝ)^6225 := by
    have hnat : (554927637 : ℕ)^8273*25000000000000^6225 ≤ 3381975659157^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554927637 2500000000 3381975659157 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369563913/10000000000 : ℝ), (5272287151/10000000000 : ℝ), (-554927637/2500000000 : ℝ)] ![(21880641032739/50000000000000 : ℝ), (42710815286537/100000000000000 : ℝ), (3381975659157/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369563913/10000000000 : ℝ)|^8273 ≤ (21880641032739/50000000000000 : ℝ)^6225
        have hw : |(5369563913/10000000000 : ℝ)|=(5369563913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272287151/10000000000 : ℝ)|^8273 ≤ (42710815286537/100000000000000 : ℝ)^6225
        have hw : |(5272287151/10000000000 : ℝ)|=(5272287151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-554927637/2500000000 : ℝ)|^8273 ≤ (3381975659157/25000000000000 : ℝ)^6225
        have hw : |(-554927637/2500000000 : ℝ)|=(554927637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_box_15 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265423157/625000000 : ℝ)*x 0 + (4438849293/10000000000 : ℝ)*x 1 + (1109712361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265423157/625000000 : ℝ)^8273 ≤ (6407987050737/20000000000000 : ℝ)^6225 := by
    have hnat : (265423157 : ℕ)^8273*20000000000000^6225 ≤ 6407987050737^6225*625000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265423157 625000000 6407987050737 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4438849293/10000000000 : ℝ)^8273 ≤ (33980031602099/100000000000000 : ℝ)^6225 := by
    have hnat : (4438849293 : ℕ)^8273*100000000000000^6225 ≤ 33980031602099^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4438849293 10000000000 33980031602099 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1109712361/2500000000 : ℝ)^8273 ≤ (33980033138321/100000000000000 : ℝ)^6225 := by
    have hnat : (1109712361 : ℕ)^8273*100000000000000^6225 ≤ 33980033138321^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109712361 2500000000 33980033138321 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265423157/625000000 : ℝ), (4438849293/10000000000 : ℝ), (1109712361/2500000000 : ℝ)] ![(6407987050737/20000000000000 : ℝ), (33980031602099/100000000000000 : ℝ), (33980033138321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265423157/625000000 : ℝ)|^8273 ≤ (6407987050737/20000000000000 : ℝ)^6225
        have hw : |(265423157/625000000 : ℝ)|=(265423157/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4438849293/10000000000 : ℝ)|^8273 ≤ (33980031602099/100000000000000 : ℝ)^6225
        have hw : |(4438849293/10000000000 : ℝ)|=(4438849293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1109712361/2500000000 : ℝ)|^8273 ≤ (33980033138321/100000000000000 : ℝ)^6225
        have hw : |(1109712361/2500000000 : ℝ)|=(1109712361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1080_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2489/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59251/100000 : ℝ) ∧ (2488/3125 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10373/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11271/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11271/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11271/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11271/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11271/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11271/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11271/100000 : ℝ) ^ (517/128 : ℝ) ≤ (14818938044565629/100000000000000000000 : ℝ) := by
    have hpowers : (11271/100000 : ℝ)^517 ≤ (14818938044565629/100000000000000000000 : ℝ)^128 := by
      have hnat : (11271 : ℕ)^517*100000000000000000000^128 ≤ 14818938044565629^128*100000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11271 100000 14818938044565629 100000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11271/100000 : ℝ)) (X := (14818938044565629/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14011/100000 : ℝ) ^ (517/128 : ℝ) ≤ (7137818137020417/20000000000000000000 : ℝ) := by
    have hpowers : (14011/100000 : ℝ)^517 ≤ (7137818137020417/20000000000000000000 : ℝ)^128 := by
      have hnat : (14011 : ℕ)^517*20000000000000000000^128 ≤ 7137818137020417^128*100000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14011 100000 7137818137020417 20000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14011/100000 : ℝ)) (X := (7137818137020417/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014818938044565629/50000000000000000000 : ℝ) ≤ (2000146739853757/2000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (50014818938044565629/50000000000000000000 : ℝ)^128 ≤ (2000146739853757/2000000000000000 : ℝ)^517 := by
      have hnat : (50014818938044565629 : ℕ)^128*2000000000000000^517 ≤ 2000146739853757^517*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014818938044565629 50000000000000000000 2000146739853757 2000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000146739853757/2000000000000000 : ℝ)) (X := (50014818938044565629/50000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025254014364833857/50000000000000000000 : ℝ) ≤ (10001250251370013/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (50025254014364833857/50000000000000000000 : ℝ)^128 ≤ (10001250251370013/10000000000000000 : ℝ)^517 := by
      have hnat : (50025254014364833857 : ℕ)^128*10000000000000000^517 ≤ 10001250251370013^517*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025254014364833857 50000000000000000000 10001250251370013 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001250251370013/10000000000000000 : ℝ)) (X := (50025254014364833857/50000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007137818137020417/10000000000000000000 : ℝ) ≤ (10001766803471241/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (10007137818137020417/10000000000000000000 : ℝ)^128 ≤ (10001766803471241/10000000000000000 : ℝ)^517 := by
      have hnat : (10007137818137020417 : ℕ)^128*10000000000000000^517 ≤ 10001766803471241^517*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007137818137020417 10000000000000000000 10001766803471241 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001766803471241/10000000000000000 : ℝ)) (X := (10007137818137020417/10000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14818938044565629/100000000000000000000 : ℝ) ≤ ((6847591554632647331/6850000000000000000 : ℝ)+2*(129138025307/68500000000000 : ℝ)*(11271/100000 : ℝ))^(517/128 : ℝ) := by
    rw [show (6847591554632647331/6850000000000000000 : ℝ)+2*(129138025307/68500000000000 : ℝ)*(11271/100000 : ℝ)=(2000146739853757/2000000000000000 : ℝ) by norm_num, show 1+2*(14818938044565629/100000000000000000000 : ℝ)=(50014818938044565629/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7137818137020417/20000000000000000000 : ℝ)+(14818938044565629/100000000000000000000 : ℝ) ≤ ((6847591554632647331/6850000000000000000 : ℝ)+(129138025307/68500000000000 : ℝ)*((14011/100000 : ℝ)+(11271/100000 : ℝ)))^(517/128 : ℝ) := by
    rw [show (6847591554632647331/6850000000000000000 : ℝ)+(129138025307/68500000000000 : ℝ)*((14011/100000 : ℝ)+(11271/100000 : ℝ))=(10001250251370013/10000000000000000 : ℝ) by norm_num, show 1+(7137818137020417/20000000000000000000 : ℝ)+(14818938044565629/100000000000000000000 : ℝ)=(50025254014364833857/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7137818137020417/20000000000000000000 : ℝ) ≤ ((6847591554632647331/6850000000000000000 : ℝ)+2*(129138025307/68500000000000 : ℝ)*(14011/100000 : ℝ))^(517/128 : ℝ) := by
    rw [show (6847591554632647331/6850000000000000000 : ℝ)+2*(129138025307/68500000000000 : ℝ)*(14011/100000 : ℝ)=(10001766803471241/10000000000000000 : ℝ) by norm_num, show 1+2*(7137818137020417/20000000000000000000 : ℝ)=(10007137818137020417/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6847591554632647331/6850000000000000000 : ℝ)*(X 1 0+X 2 0)+(129138025307/68500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (11271/100000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (6847591554632647331/6850000000000000000 : ℝ)) (alpha := (129138025307/68500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6847591554632647331/6850000000000000000 : ℝ)*(X 0 1+X 2 1)+(129138025307/68500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (11271/100000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (6847591554632647331/6850000000000000000 : ℝ)) (alpha := (129138025307/68500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6847591554632647331/6850000000000000000 : ℝ)*(X 0 2+X 1 2)+(129138025307/68500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (11271/100000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (6847591554632647331/6850000000000000000 : ℝ)) (alpha := (129138025307/68500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1033958061/5000000000 : ℝ)*X 0 0+(5377176671/10000000000 : ℝ)*X 0 1+(33607351/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647679/5000000 : ℝ)*X 1 0+(-544678589/2500000000 : ℝ)*X 1 1+(672147051/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647678993/5000000000 : ℝ)*X 2 0+(2688588201/5000000000 : ℝ)*X 2 1+(-2178714383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((280106977/625000000 : ℝ)*X 0 0+(4321522287/10000000000 : ℝ)*X 0 1+(4321521747/10000000000 : ℝ)*X 0 2+(280106977/625000000 : ℝ)*X 1 0+(4321522287/10000000000 : ℝ)*X 1 1+(4321521747/10000000000 : ℝ)*X 1 2+(280106977/625000000 : ℝ)*X 2 0+(4321522287/10000000000 : ℝ)*X 2 1+(4321521747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1163631323/5000000000 : ℝ)*X 0 0+(1320073801/2500000000 : ℝ)*X 0 1+(5280295601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((536390031/1000000000 : ℝ)*X 1 0+(-2216634493/10000000000 : ℝ)*X 1 1+(660036943/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1340975117/2500000000 : ℝ)*X 2 0+(660036969/1250000000 : ℝ)*X 2 1+(-443326801/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2132460691/5000000000 : ℝ)*X 0 0+(2214948061/5000000000 : ℝ)*X 0 1+(2214947741/5000000000 : ℝ)*X 0 2+(2132460691/5000000000 : ℝ)*X 1 0+(2214948061/5000000000 : ℝ)*X 1 1+(2214947741/5000000000 : ℝ)*X 1 2+(2132460691/5000000000 : ℝ)*X 2 0+(2214948061/5000000000 : ℝ)*X 2 1+(2214947741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2273104107/10000000000 : ℝ)*X 0 0+(5214528577/10000000000 : ℝ)*X 0 1+(5386778697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644280353/5000000000 : ℝ)*X 1 0+(-67965151/312500000 : ℝ)*X 1 1+(1077355859/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322140171/2500000000 : ℝ)*X 2 0+(5386778613/10000000000 : ℝ)*X 2 1+(-2174885781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2251463009/5000000000 : ℝ)*X 0 0+(4310774273/10000000000 : ℝ)*X 0 1+(862154863/2000000000 : ℝ)*X 0 2+(2251463009/5000000000 : ℝ)*X 1 0+(4310774273/10000000000 : ℝ)*X 1 1+(862154863/2000000000 : ℝ)*X 1 2+(2251463009/5000000000 : ℝ)*X 2 0+(4310774273/10000000000 : ℝ)*X 2 1+(862154863/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-84897347/400000000 : ℝ)*X 0 0+(217664759/400000000 : ℝ)*X 0 1+(5272287117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((53695641/100000000 : ℝ)*X 1 0+(-2219710713/10000000000 : ℝ)*X 1 1+(5272286839/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369563913/10000000000 : ℝ)*X 2 0+(5272287151/10000000000 : ℝ)*X 2 1+(-554927637/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((265423157/625000000 : ℝ)*X 0 0+(4438849293/10000000000 : ℝ)*X 0 1+(1109712361/2500000000 : ℝ)*X 0 2+(265423157/625000000 : ℝ)*X 1 0+(4438849293/10000000000 : ℝ)*X 1 1+(1109712361/2500000000 : ℝ)*X 1 2+(265423157/625000000 : ℝ)*X 2 0+(4438849293/10000000000 : ℝ)*X 2 1+(1109712361/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2489/4000 : ℝ) ≤ (-213113440034187262057278394544397/342500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27257789/100000000000000 : ℝ)*(upper1) + (221424021/100000000000000 : ℝ)*(lower2) + (29126961/50000000000000 : ℝ)*(upper4) + (3764257/100000000000000 : ℝ)*(upper5) + (3868401460903771/100000000000000 : ℝ)*(major0) + (3868401460903771/100000000000000 : ℝ)*(major1) + (3868401460903771/100000000000000 : ℝ)*(major2) + (53888689/25000000000000 : ℝ)*(sp1) + (116009487/10000000000000 : ℝ)*(sp3) + (2574219485547629/50000000000000 : ℝ)*(sp4) + (5148438755540501/100000000000000 : ℝ)*(sp5) + (2574045691023519/50000000000000 : ℝ)*(sp6) + (163068984876083/6250000000000 : ℝ)*(sp7) + (17379452411/5000000000000 : ℝ)*(sp14) + (1304552459056099/50000000000000 : ℝ)*(f.failure) + (2574219485547629/50000000000000 : ℝ)*(f.sum) + (1840013779797/3425000000000000000000000000 : ℝ)*base65 + (10122897072689314799/685000000000000000000000000000000 : ℝ)*base68 + (37298001299314799/685000000000000000000000000000000 : ℝ)*base70 + (5472206043330685201/685000000000000000000000000000000 : ℝ)*base71 + (1132033013079/107031250000000000000000000 : ℝ)*base74 + (3820715203910685201/685000000000000000000000000000000 : ℝ)*base75 + (1994975760459314799/685000000000000000000000000000000 : ℝ)*base78 + (1215472970029314799/685000000000000000000000000000000 : ℝ)*base80 + (15016003274397/3425000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (26076369/2500000000000000000000 : ℝ)*base89 + (26076369/2500000000000000000000 : ℝ)*base91 + (26076369/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59251/100000 : ℝ) ≤ (101472007551069761628926037616323/171250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2904847/6250000000000 : ℝ)*(upper3) + (4131163/5000000000000 : ℝ)*(upper4) + (160462427/100000000000000 : ℝ)*(lower5) + (3931566918020811/100000000000000 : ℝ)*(major0) + (3931566918020811/100000000000000 : ℝ)*(major1) + (3931566918020811/100000000000000 : ℝ)*(major2) + (5191663783119109/100000000000000 : ℝ)*(sp0) + (5191667320291113/100000000000000 : ℝ)*(sp1) + (5191654205581179/100000000000000 : ℝ)*(sp2) + (1325847469191267/50000000000000 : ℝ)*(sp3) + (296306833/4000000000000 : ℝ)*(sp5) + (20522380759/100000000000000 : ℝ)*(sp6) + (12927351437/100000000000000 : ℝ)*(sp7) + (10944842829/100000000000000 : ℝ)*(sp8) + (265170786573397/10000000000000 : ℝ)*(f.failure) + (2595837363980969/50000000000000 : ℝ)*(f.sum) + (853848436763/856250000000000000000000000 : ℝ)*base65 + (1353545612860694559/685000000000000000000000000000000 : ℝ)*base68 + (520657719554305441/685000000000000000000000000000000 : ℝ)*base69 + (3001777630540694559/685000000000000000000000000000000 : ℝ)*base72 + (2963832409451/1712500000000000000000000000 : ℝ)*base73 + (2600415076380694559/685000000000000000000000000000000 : ℝ)*base76 + (1299094335400694559/685000000000000000000000000000000 : ℝ)*base78 + (5439737241850694559/685000000000000000000000000000000 : ℝ)*base80 + (6837616927523/3425000000000000000000000000 : ℝ)*base82 + (3442793/500000000000000000000 : ℝ)*base90 + (3442793/500000000000000000000 : ℝ)*base92 + (3442793/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (2488/3125 : ℝ) ≤ (995233559842996269500033727693/1250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157715859/100000000000000 : ℝ)*(upper0) + (8937343/50000000000000 : ℝ)*(lower1) + (248577283/100000000000000 : ℝ)*(upper2) + (581226807/100000000000000 : ℝ)*(lower5) + (2199873438648563/50000000000000 : ℝ)*(major0) + (2199873438648563/50000000000000 : ℝ)*(major1) + (2199873438648563/50000000000000 : ℝ)*(major2) + (2000243197/50000000000000 : ℝ)*(sp0) + (173455229719/50000000000000 : ℝ)*(sp1) + (177011423137/100000000000000 : ℝ)*(sp3) + (5805470903709679/100000000000000 : ℝ)*(sp8) + (1161025598747327/20000000000000 : ℝ)*(sp9) + (5805474904196073/100000000000000 : ℝ)*(sp10) + (1483651138689609/50000000000000 : ℝ)*(sp11) + (593495857760471/20000000000000 : ℝ)*(f.failure) + (5805474904196073/100000000000000 : ℝ)*(f.sum) + (86708786111/25000000000000000000000000 : ℝ)*base65 + (5021400068890769/2500000000000000000000000000000 : ℝ)*base67 + (1854406763890769/2500000000000000000000000000000 : ℝ)*base69 + (19791230498890769/2500000000000000000000000000000 : ℝ)*base71 + (655165533839/25000000000000000000000000 : ℝ)*base74 + (23706682551109231/2500000000000000000000000000000 : ℝ)*base76 + (25709916443890769/2500000000000000000000000000000 : ℝ)*base77 + (102649288911109231/2500000000000000000000000000000 : ℝ)*base80 + (23435359557/12500000000000000000000000 : ℝ)*base82 + (923699/1000000000000000000000 : ℝ)*base90 + (923699/1000000000000000000000 : ℝ)*base92 + (923699/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-10373/12500 : ℝ) ≤ (-142106542267230845986470265829559/171250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2216659/12500000000000 : ℝ)*(upper3) + (124391/3125000000000 : ℝ)*(lower4) + (20503279/20000000000000 : ℝ)*(upper5) + (2217182342361937/50000000000000 : ℝ)*(major0) + (2217182342361937/50000000000000 : ℝ)*(major1) + (2217182342361937/50000000000000 : ℝ)*(major2) + (970849827/50000000000000 : ℝ)*(sp4) + (229079367009/100000000000000 : ℝ)*(sp5) + (41127338523/100000000000000 : ℝ)*(sp6) + (5218740793/12500000000000 : ℝ)*(sp7) + (2952780124364771/50000000000000 : ℝ)*(sp12) + (5905333111062187/100000000000000 : ℝ)*(sp13) + (5905521063090673/100000000000000 : ℝ)*(sp14) + (2990786069922809/100000000000000 : ℝ)*(sp15) + (2990827819849153/100000000000000 : ℝ)*(f.failure) + (1476390547607299/25000000000000 : ℝ)*(f.sum) + (5313309396633/856250000000000000000000000 : ℝ)*base66 + (831692788672559853/342500000000000000000000000000000 : ℝ)*base68 + (2000918467015059853/342500000000000000000000000000000 : ℝ)*base70 + (903095214160059853/342500000000000000000000000000000 : ℝ)*base72 + (7217816907407/3425000000000000000000000000 : ℝ)*base74 + (598439963042440147/342500000000000000000000000000000 : ℝ)*base75 + (471631771787559853/342500000000000000000000000000000 : ℝ)*base78 + (1341888228174940147/342500000000000000000000000000000 : ℝ)*base79 + (17792303524307/3425000000000000000000000000 : ℝ)*base82 + (19926843/5000000000000000000000 : ℝ)*base89 + (19926843/5000000000000000000000 : ℝ)*base91 + (19926843/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1080_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59251/100000 : ℝ) else (2488/3125 : ℝ) ≤ X j i ∧ X j i ≤ (10373/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1080_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1080_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59251/100000 : ℝ) else (2488/3125 : ℝ) ≤ X j i ∧ X j i ≤ (10373/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1080_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1080_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59251/100000 : ℝ) else (2488/3125 : ℝ) ≤ X j i ∧ X j i ≤ (10373/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1080_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
