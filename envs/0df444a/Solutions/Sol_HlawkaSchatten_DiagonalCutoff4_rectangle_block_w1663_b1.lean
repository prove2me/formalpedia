-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1663_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:58.536141+00:00
-- url     : https://prove2.me/submissions/bcef369a-6a54-42d5-beb9-0f4f43b2e127

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
theorem support_rectangle_w1663_s3_0 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-789710067/5000000000 : ℝ)*x 0 + (2721881243/5000000000 : ℝ)*x 1 + (5184651751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (789710067/5000000000 : ℝ)^4971 ≤ (9784933335221/100000000000000 : ℝ)^3947 := by
    have hnat : (789710067 : ℕ)^4971*100000000000000^3947 ≤ 9784933335221^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789710067 5000000000 9784933335221 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721881243/5000000000 : ℝ)^4971 ≤ (23246174886167/50000000000000 : ℝ)^3947 := by
    have hnat : (2721881243 : ℕ)^4971*50000000000000^3947 ≤ 23246174886167^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721881243 5000000000 23246174886167 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184651751/10000000000 : ℝ)^4971 ≤ (43722716880621/100000000000000 : ℝ)^3947 := by
    have hnat : (5184651751 : ℕ)^4971*100000000000000^3947 ≤ 43722716880621^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184651751 10000000000 43722716880621 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-789710067/5000000000 : ℝ), (2721881243/5000000000 : ℝ), (5184651751/10000000000 : ℝ)] ![(9784933335221/100000000000000 : ℝ), (23246174886167/50000000000000 : ℝ), (43722716880621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-789710067/5000000000 : ℝ)|^4971 ≤ (9784933335221/100000000000000 : ℝ)^3947
        have hw : |(-789710067/5000000000 : ℝ)|=(789710067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721881243/5000000000 : ℝ)|^4971 ≤ (23246174886167/50000000000000 : ℝ)^3947
        have hw : |(2721881243/5000000000 : ℝ)|=(2721881243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184651751/10000000000 : ℝ)|^4971 ≤ (43722716880621/100000000000000 : ℝ)^3947
        have hw : |(5184651751/10000000000 : ℝ)|=(5184651751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s3_1 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345783891/10000000000 : ℝ)*x 0 + (-4281853/25000000 : ℝ)*x 1 + (1296162931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345783891/10000000000 : ℝ)^4971 ≤ (45440943704117/100000000000000 : ℝ)^3947 := by
    have hnat : (5345783891 : ℕ)^4971*100000000000000^3947 ≤ 45440943704117^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345783891 10000000000 45440943704117 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4281853/25000000 : ℝ)^4971 ≤ (86690717503/800000000000 : ℝ)^3947 := by
    have hnat : (4281853 : ℕ)^4971*800000000000^3947 ≤ 86690717503^3947*25000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281853 25000000 86690717503 800000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296162931/2500000000 : ℝ)^4971 ≤ (8744543318771/20000000000000 : ℝ)^3947 := by
    have hnat : (1296162931 : ℕ)^4971*20000000000000^3947 ≤ 8744543318771^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296162931 2500000000 8744543318771 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345783891/10000000000 : ℝ), (-4281853/25000000 : ℝ), (1296162931/2500000000 : ℝ)] ![(45440943704117/100000000000000 : ℝ), (86690717503/800000000000 : ℝ), (8744543318771/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345783891/10000000000 : ℝ)|^4971 ≤ (45440943704117/100000000000000 : ℝ)^3947
        have hw : |(5345783891/10000000000 : ℝ)|=(5345783891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4281853/25000000 : ℝ)|^4971 ≤ (86690717503/800000000000 : ℝ)^3947
        have hw : |(-4281853/25000000 : ℝ)|=(4281853/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296162931/2500000000 : ℝ)|^4971 ≤ (8744543318771/20000000000000 : ℝ)^3947
        have hw : |(1296162931/2500000000 : ℝ)|=(1296162931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s3_2 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345783899/10000000000 : ℝ)*x 0 + (324040733/625000000 : ℝ)*x 1 + (-26761581/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345783899/10000000000 : ℝ)^4971 ≤ (22720471894881/50000000000000 : ℝ)^3947 := by
    have hnat : (5345783899 : ℕ)^4971*50000000000000^3947 ≤ 22720471894881^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345783899 10000000000 22720471894881 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324040733/625000000 : ℝ)^4971 ≤ (43722716636339/100000000000000 : ℝ)^3947 := by
    have hnat : (324040733 : ℕ)^4971*100000000000000^3947 ≤ 43722716636339^3947*625000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324040733 625000000 43722716636339 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26761581/156250000 : ℝ)^4971 ≤ (5418169780191/50000000000000 : ℝ)^3947 := by
    have hnat : (26761581 : ℕ)^4971*50000000000000^3947 ≤ 5418169780191^3947*156250000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26761581 156250000 5418169780191 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345783899/10000000000 : ℝ), (324040733/625000000 : ℝ), (-26761581/156250000 : ℝ)] ![(22720471894881/50000000000000 : ℝ), (43722716636339/100000000000000 : ℝ), (5418169780191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345783899/10000000000 : ℝ)|^4971 ≤ (22720471894881/50000000000000 : ℝ)^3947
        have hw : |(5345783899/10000000000 : ℝ)|=(5345783899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324040733/625000000 : ℝ)|^4971 ≤ (43722716636339/100000000000000 : ℝ)^3947
        have hw : |(324040733/625000000 : ℝ)|=(324040733/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26761581/156250000 : ℝ)|^4971 ≤ (5418169780191/50000000000000 : ℝ)^3947
        have hw : |(-26761581/156250000 : ℝ)|=(26761581/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s3_3 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (417086913/1000000000 : ℝ)*x 0 + (1920041917/5000000000 : ℝ)*x 1 + (904291881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417086913/1000000000 : ℝ)^4971 ≤ (8310728270313/25000000000000 : ℝ)^3947 := by
    have hnat : (417086913 : ℕ)^4971*25000000000000^3947 ≤ 8310728270313^3947*1000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417086913 1000000000 8310728270313 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1920041917/5000000000 : ℝ)^4971 ≤ (14978664112841/50000000000000 : ℝ)^3947 := by
    have hnat : (1920041917 : ℕ)^4971*50000000000000^3947 ≤ 14978664112841^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920041917 5000000000 14978664112841 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904291881/2000000000 : ℝ)^4971 ≤ (18399879339291/50000000000000 : ℝ)^3947 := by
    have hnat : (904291881 : ℕ)^4971*50000000000000^3947 ≤ 18399879339291^3947*2000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904291881 2000000000 18399879339291 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(417086913/1000000000 : ℝ), (1920041917/5000000000 : ℝ), (904291881/2000000000 : ℝ)] ![(8310728270313/25000000000000 : ℝ), (14978664112841/50000000000000 : ℝ), (18399879339291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(417086913/1000000000 : ℝ)|^4971 ≤ (8310728270313/25000000000000 : ℝ)^3947
        have hw : |(417086913/1000000000 : ℝ)|=(417086913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1920041917/5000000000 : ℝ)|^4971 ≤ (14978664112841/50000000000000 : ℝ)^3947
        have hw : |(1920041917/5000000000 : ℝ)|=(1920041917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904291881/2000000000 : ℝ)|^4971 ≤ (18399879339291/50000000000000 : ℝ)^3947
        have hw : |(904291881/2000000000 : ℝ)|=(904291881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s3_4 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-394870721/2500000000 : ℝ)*x 0 + (648328007/1250000000 : ℝ)*x 1 + (1360442317/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (394870721/2500000000 : ℝ)^4971 ≤ (978542294807/10000000000000 : ℝ)^3947 := by
    have hnat : (394870721 : ℕ)^4971*10000000000000^3947 ≤ 978542294807^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394870721 2500000000 978542294807 10000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648328007/1250000000 : ℝ)^4971 ≤ (8748733141339/20000000000000 : ℝ)^3947 := by
    have hnat : (648328007 : ℕ)^4971*20000000000000^3947 ≤ 8748733141339^3947*1250000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648328007 1250000000 8748733141339 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360442317/2500000000 : ℝ)^4971 ≤ (9294182266907/20000000000000 : ℝ)^3947 := by
    have hnat : (1360442317 : ℕ)^4971*20000000000000^3947 ≤ 9294182266907^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360442317 2500000000 9294182266907 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-394870721/2500000000 : ℝ), (648328007/1250000000 : ℝ), (1360442317/2500000000 : ℝ)] ![(978542294807/10000000000000 : ℝ), (8748733141339/20000000000000 : ℝ), (9294182266907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-394870721/2500000000 : ℝ)|^4971 ≤ (978542294807/10000000000000 : ℝ)^3947
        have hw : |(-394870721/2500000000 : ℝ)|=(394870721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(648328007/1250000000 : ℝ)|^4971 ≤ (8748733141339/20000000000000 : ℝ)^3947
        have hw : |(648328007/1250000000 : ℝ)|=(648328007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360442317/2500000000 : ℝ)|^4971 ≤ (9294182266907/20000000000000 : ℝ)^3947
        have hw : |(1360442317/2500000000 : ℝ)|=(1360442317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s3_5 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638231267/5000000000 : ℝ)*x 0 + (-45488239/312500000 : ℝ)*x 1 + (1360442309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638231267/5000000000 : ℝ)^4971 ≤ (11175016669617/25000000000000 : ℝ)^3947 := by
    have hnat : (2638231267 : ℕ)^4971*25000000000000^3947 ≤ 11175016669617^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638231267 5000000000 11175016669617 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45488239/312500000 : ℝ)^4971 ≤ (882902231073/10000000000000 : ℝ)^3947 := by
    have hnat : (45488239 : ℕ)^4971*10000000000000^3947 ≤ 882902231073^3947*312500000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45488239 312500000 882902231073 10000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360442309/2500000000 : ℝ)^4971 ≤ (46470910990369/100000000000000 : ℝ)^3947 := by
    have hnat : (1360442309 : ℕ)^4971*100000000000000^3947 ≤ 46470910990369^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360442309 2500000000 46470910990369 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638231267/5000000000 : ℝ), (-45488239/312500000 : ℝ), (1360442309/2500000000 : ℝ)] ![(11175016669617/25000000000000 : ℝ), (882902231073/10000000000000 : ℝ), (46470910990369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638231267/5000000000 : ℝ)|^4971 ≤ (11175016669617/25000000000000 : ℝ)^3947
        have hw : |(2638231267/5000000000 : ℝ)|=(2638231267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45488239/312500000 : ℝ)|^4971 ≤ (882902231073/10000000000000 : ℝ)^3947
        have hw : |(-45488239/312500000 : ℝ)|=(45488239/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360442309/2500000000 : ℝ)|^4971 ≤ (46470910990369/100000000000000 : ℝ)^3947
        have hw : |(1360442309/2500000000 : ℝ)|=(1360442309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s3_6 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527646243/1000000000 : ℝ)*x 0 + (5441769441/10000000000 : ℝ)*x 1 + (-727811753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527646243/1000000000 : ℝ)^4971 ≤ (8940013113769/20000000000000 : ℝ)^3947 := by
    have hnat : (527646243 : ℕ)^4971*20000000000000^3947 ≤ 8940013113769^3947*1000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527646243 1000000000 8940013113769 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441769441/10000000000 : ℝ)^4971 ≤ (46470913195181/100000000000000 : ℝ)^3947 := by
    have hnat : (5441769441 : ℕ)^4971*100000000000000^3947 ≤ 46470913195181^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441769441 10000000000 46470913195181 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (727811753/5000000000 : ℝ)^4971 ≤ (8829021225983/100000000000000 : ℝ)^3947 := by
    have hnat : (727811753 : ℕ)^4971*100000000000000^3947 ≤ 8829021225983^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727811753 5000000000 8829021225983 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527646243/1000000000 : ℝ), (5441769441/10000000000 : ℝ), (-727811753/5000000000 : ℝ)] ![(8940013113769/20000000000000 : ℝ), (46470913195181/100000000000000 : ℝ), (8829021225983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527646243/1000000000 : ℝ)|^4971 ≤ (8940013113769/20000000000000 : ℝ)^3947
        have hw : |(527646243/1000000000 : ℝ)|=(527646243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441769441/10000000000 : ℝ)|^4971 ≤ (46470913195181/100000000000000 : ℝ)^3947
        have hw : |(5441769441/10000000000 : ℝ)|=(5441769441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-727811753/5000000000 : ℝ)|^4971 ≤ (8829021225983/100000000000000 : ℝ)^3947
        have hw : |(-727811753/5000000000 : ℝ)|=(727811753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s3_7 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042758409/2500000000 : ℝ)*x 0 + (564534103/1250000000 : ℝ)*x 1 + (3845325123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042758409/2500000000 : ℝ)^4971 ≤ (33244564408367/100000000000000 : ℝ)^3947 := by
    have hnat : (1042758409 : ℕ)^4971*100000000000000^3947 ≤ 33244564408367^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042758409 2500000000 33244564408367 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564534103/1250000000 : ℝ)^4971 ≤ (3674660179769/10000000000000 : ℝ)^3947 := by
    have hnat : (564534103 : ℕ)^4971*10000000000000^3947 ≤ 3674660179769^3947*1250000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564534103 1250000000 3674660179769 10000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3845325123/10000000000 : ℝ)^4971 ≤ (30008833769347/100000000000000 : ℝ)^3947 := by
    have hnat : (3845325123 : ℕ)^4971*100000000000000^3947 ≤ 30008833769347^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3845325123 10000000000 30008833769347 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042758409/2500000000 : ℝ), (564534103/1250000000 : ℝ), (3845325123/10000000000 : ℝ)] ![(33244564408367/100000000000000 : ℝ), (3674660179769/10000000000000 : ℝ), (30008833769347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042758409/2500000000 : ℝ)|^4971 ≤ (33244564408367/100000000000000 : ℝ)^3947
        have hw : |(1042758409/2500000000 : ℝ)|=(1042758409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564534103/1250000000 : ℝ)|^4971 ≤ (3674660179769/10000000000000 : ℝ)^3947
        have hw : |(564534103/1250000000 : ℝ)|=(564534103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3845325123/10000000000 : ℝ)|^4971 ≤ (30008833769347/100000000000000 : ℝ)^3947
        have hw : |(3845325123/10000000000 : ℝ)|=(3845325123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1663_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (267/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (10733/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3249/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1019/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (267/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1019/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (267/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1019/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (267/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1019/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (267/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1019/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (267/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1019/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (267/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (267/2500 : ℝ) ^ (4967/1024 : ℝ) ≤ (1940892040550733/100000000000000000000 : ℝ) := by
    have hpowers : (267/2500 : ℝ)^4967 ≤ (1940892040550733/100000000000000000000 : ℝ)^1024 := by
      have hnat : (267 : ℕ)^4967*100000000000000000000^1024 ≤ 1940892040550733^1024*2500^4967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        267 2500 1940892040550733 100000000000000000000 4967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (267/2500 : ℝ)) (X := (1940892040550733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1019/6250 : ℝ) ^ (4967/1024 : ℝ) ≤ (15106545459361131/100000000000000000000 : ℝ) := by
    have hpowers : (1019/6250 : ℝ)^4967 ≤ (15106545459361131/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1019 : ℕ)^4967*100000000000000000000^1024 ≤ 15106545459361131^1024*6250^4967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1019 6250 15106545459361131 100000000000000000000 4967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1019/6250 : ℝ)) (X := (15106545459361131/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001940892040550733/50000000000000000000 : ℝ) ≤ (10000080025883959/10000000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (50001940892040550733/50000000000000000000 : ℝ)^1024 ≤ (10000080025883959/10000000000000000 : ℝ)^4967 := by
      have hnat : (50001940892040550733 : ℕ)^1024*10000000000000000^4967 ≤ 10000080025883959^4967*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001940892040550733 50000000000000000000 10000080025883959 10000000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000080025883959/10000000000000000 : ℝ)) (X := (50001940892040550733/50000000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12502130929687488983/12500000000000000000 : ℝ) ≤ (2000070285463771/2000000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (12502130929687488983/12500000000000000000 : ℝ)^1024 ≤ (2000070285463771/2000000000000000 : ℝ)^4967 := by
      have hnat : (12502130929687488983 : ℕ)^1024*2000000000000000^4967 ≤ 2000070285463771^4967*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502130929687488983 12500000000000000000 2000070285463771 2000000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000070285463771/2000000000000000 : ℝ)) (X := (12502130929687488983/12500000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015106545459361131/50000000000000000000 : ℝ) ≤ (10000622828753751/10000000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (50015106545459361131/50000000000000000000 : ℝ)^1024 ≤ (10000622828753751/10000000000000000 : ℝ)^4967 := by
      have hnat : (50015106545459361131 : ℕ)^1024*10000000000000000^4967 ≤ 10000622828753751^4967*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015106545459361131 50000000000000000000 10000622828753751 10000000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000622828753751/10000000000000000 : ℝ)) (X := (50015106545459361131/50000000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1940892040550733/100000000000000000000 : ℝ) ≤ ((7029331616365250857/7030000000000000000 : ℝ)+2*(16962589681/35150000000000 : ℝ)*(267/2500 : ℝ))^(4967/1024 : ℝ) := by
    rw [show (7029331616365250857/7030000000000000000 : ℝ)+2*(16962589681/35150000000000 : ℝ)*(267/2500 : ℝ)=(10000080025883959/10000000000000000 : ℝ) by norm_num, show 1+2*(1940892040550733/100000000000000000000 : ℝ)=(50001940892040550733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15106545459361131/100000000000000000000 : ℝ)+(1940892040550733/100000000000000000000 : ℝ) ≤ ((7029331616365250857/7030000000000000000 : ℝ)+(16962589681/35150000000000 : ℝ)*((1019/6250 : ℝ)+(267/2500 : ℝ)))^(4967/1024 : ℝ) := by
    rw [show (7029331616365250857/7030000000000000000 : ℝ)+(16962589681/35150000000000 : ℝ)*((1019/6250 : ℝ)+(267/2500 : ℝ))=(2000070285463771/2000000000000000 : ℝ) by norm_num, show 1+(15106545459361131/100000000000000000000 : ℝ)+(1940892040550733/100000000000000000000 : ℝ)=(12502130929687488983/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15106545459361131/100000000000000000000 : ℝ) ≤ ((7029331616365250857/7030000000000000000 : ℝ)+2*(16962589681/35150000000000 : ℝ)*(1019/6250 : ℝ))^(4967/1024 : ℝ) := by
    rw [show (7029331616365250857/7030000000000000000 : ℝ)+2*(16962589681/35150000000000 : ℝ)*(1019/6250 : ℝ)=(10000622828753751/10000000000000000 : ℝ) by norm_num, show 1+2*(15106545459361131/100000000000000000000 : ℝ)=(50015106545459361131/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7029331616365250857/7030000000000000000 : ℝ)*(X 1 0+X 2 0)+(16962589681/35150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (267/2500 : ℝ)) (hi := (1019/6250 : ℝ)) (c := (7029331616365250857/7030000000000000000 : ℝ)) (alpha := (16962589681/35150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7029331616365250857/7030000000000000000 : ℝ)*(X 0 1+X 2 1)+(16962589681/35150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (267/2500 : ℝ)) (hi := (1019/6250 : ℝ)) (c := (7029331616365250857/7030000000000000000 : ℝ)) (alpha := (16962589681/35150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7029331616365250857/7030000000000000000 : ℝ)*(X 0 2+X 1 2)+(16962589681/35150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (267/2500 : ℝ)) (hi := (1019/6250 : ℝ)) (c := (7029331616365250857/7030000000000000000 : ℝ)) (alpha := (16962589681/35150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-789710067/5000000000 : ℝ)*X 0 0+(2721881243/5000000000 : ℝ)*X 0 1+(5184651751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345783891/10000000000 : ℝ)*X 1 0+(-4281853/25000000 : ℝ)*X 1 1+(1296162931/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345783899/10000000000 : ℝ)*X 2 0+(324040733/625000000 : ℝ)*X 2 1+(-26761581/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((417086913/1000000000 : ℝ)*X 0 0+(1920041917/5000000000 : ℝ)*X 0 1+(904291881/2000000000 : ℝ)*X 0 2+(417086913/1000000000 : ℝ)*X 1 0+(1920041917/5000000000 : ℝ)*X 1 1+(904291881/2000000000 : ℝ)*X 1 2+(417086913/1000000000 : ℝ)*X 2 0+(1920041917/5000000000 : ℝ)*X 2 1+(904291881/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-394870721/2500000000 : ℝ)*X 0 0+(648328007/1250000000 : ℝ)*X 0 1+(1360442317/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638231267/5000000000 : ℝ)*X 1 0+(-45488239/312500000 : ℝ)*X 1 1+(1360442309/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((527646243/1000000000 : ℝ)*X 2 0+(5441769441/10000000000 : ℝ)*X 2 1+(-727811753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1042758409/2500000000 : ℝ)*X 0 0+(564534103/1250000000 : ℝ)*X 0 1+(3845325123/10000000000 : ℝ)*X 0 2+(1042758409/2500000000 : ℝ)*X 1 0+(564534103/1250000000 : ℝ)*X 1 1+(3845325123/10000000000 : ℝ)*X 1 2+(1042758409/2500000000 : ℝ)*X 2 0+(564534103/1250000000 : ℝ)*X 2 1+(3845325123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1169946615684032660627392209/351500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (495545957/100000000000000 : ℝ)*(base19) + (234880149/50000000000000 : ℝ)*(base23) + (4217987/25000000000000 : ℝ)*(lower2) + (34172567/50000000000000 : ℝ)*(upper3) + (59608213/100000000000000 : ℝ)*(upper5) + (2663495064147393/100000000000000 : ℝ)*(major0) + (2663495064147393/100000000000000 : ℝ)*(major1) + (2663495064147393/100000000000000 : ℝ)*(major2) + (964839960171393/25000000000000 : ℝ)*(sp0) + (1929682781210881/50000000000000 : ℝ)*(sp1) + (3859365588207421/100000000000000 : ℝ)*(sp2) + (91726348722251/6250000000000 : ℝ)*(sp3) + (6217282147/100000000000000 : ℝ)*(sp4) + (47596461/2000000000000 : ℝ)*(sp7) + (733811979689533/50000000000000 : ℝ)*(f.failure) + (3859366057967719/100000000000000 : ℝ)*(f.sum) + (9275187274997/1757500000000000000000000000 : ℝ)*base66 + (6306041430309834199/703000000000000000000000000000000 : ℝ)*base68 + (1858787386799834199/703000000000000000000000000000000 : ℝ)*base70 + (1559324307271834199/703000000000000000000000000000000 : ℝ)*base72 + (10111628731447/1757500000000000000000000000 : ℝ)*base74 + (472838858959834199/703000000000000000000000000000000 : ℝ)*base76 + (5219619318782834199/703000000000000000000000000000000 : ℝ)*base78 + (517183194901834199/703000000000000000000000000000000 : ℝ)*base80 + (1217271339403/439375000000000000000000000 : ℝ)*base82 + (38896953/2500000000000000000000 : ℝ)*base89 + (38896953/2500000000000000000000 : ℝ)*base91 + (38896953/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56096441715660378995872647/21968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (232226193/50000000000000 : ℝ)*(base19) + (552275247/100000000000000 : ℝ)*(base23) + (62599219/100000000000000 : ℝ)*(upper2) + (8203199/10000000000000 : ℝ)*(upper3) + (2446143/3125000000000 : ℝ)*(upper5) + (169055136323469/6250000000000 : ℝ)*(major0) + (169055136323469/6250000000000 : ℝ)*(major1) + (169055136323469/6250000000000 : ℝ)*(major2) + (4555669927/100000000000000 : ℝ)*(sp1) + (8090104131/100000000000000 : ℝ)*(sp2) + (1959667711561649/50000000000000 : ℝ)*(sp4) + (1959665201500493/50000000000000 : ℝ)*(sp5) + (48991584759299/1250000000000 : ℝ)*(sp6) + (1490428854112191/100000000000000 : ℝ)*(sp7) + (1490428854112191/100000000000000 : ℝ)*(f.failure) + (1959667711561649/50000000000000 : ℝ)*(f.sum) + (1789094320303/878750000000000000000000000 : ℝ)*base66 + (348790493229237067/43937500000000000000000000000000 : ℝ)*base68 + (272604023126424567/43937500000000000000000000000000 : ℝ)*base70 + (176327320738924567/43937500000000000000000000000000 : ℝ)*base72 + (277897341451/439375000000000000000000000 : ℝ)*base73 + (670535634435174567/43937500000000000000000000000000 : ℝ)*base76 + (343303348567924567/43937500000000000000000000000000 : ℝ)*base78 + (679674157054237067/43937500000000000000000000000000 : ℝ)*base80 + (9659260308913/3515000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (20664531/5000000000000000000000 : ℝ)*base89 + (20664531/5000000000000000000000 : ℝ)*base91 + (20664531/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1663_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (267/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10733/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3249/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1663_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1663_s4_0 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-789726781/5000000000 : ℝ)*x 0 + (2721796567/5000000000 : ℝ)*x 1 + (51847987/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (789726781/5000000000 : ℝ)^4971 ≤ (1957038831949/20000000000000 : ℝ)^3947 := by
    have hnat : (789726781 : ℕ)^4971*20000000000000^3947 ≤ 1957038831949^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789726781 5000000000 1957038831949 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721796567/5000000000 : ℝ)^4971 ≤ (46490528195301/100000000000000 : ℝ)^3947 := by
    have hnat : (2721796567 : ℕ)^4971*100000000000000^3947 ≤ 46490528195301^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721796567 5000000000 46490528195301 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51847987/100000000 : ℝ)^4971 ≤ (43724277627297/100000000000000 : ℝ)^3947 := by
    have hnat : (51847987 : ℕ)^4971*100000000000000^3947 ≤ 43724277627297^3947*100000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51847987 100000000 43724277627297 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-789726781/5000000000 : ℝ), (2721796567/5000000000 : ℝ), (51847987/100000000 : ℝ)] ![(1957038831949/20000000000000 : ℝ), (46490528195301/100000000000000 : ℝ), (43724277627297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-789726781/5000000000 : ℝ)|^4971 ≤ (1957038831949/20000000000000 : ℝ)^3947
        have hw : |(-789726781/5000000000 : ℝ)|=(789726781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721796567/5000000000 : ℝ)|^4971 ≤ (46490528195301/100000000000000 : ℝ)^3947
        have hw : |(2721796567/5000000000 : ℝ)|=(2721796567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51847987/100000000 : ℝ)|^4971 ≤ (43724277627297/100000000000000 : ℝ)^3947
        have hw : |(51847987/100000000 : ℝ)|=(51847987/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s4_1 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668217197/1250000000 : ℝ)*x 0 + (-428151741/2500000000 : ℝ)*x 1 + (1296199779/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668217197/1250000000 : ℝ)^4971 ≤ (2272022393651/5000000000000 : ℝ)^3947 := by
    have hnat : (668217197 : ℕ)^4971*5000000000000^3947 ≤ 2272022393651^3947*1250000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668217197 1250000000 2272022393651 5000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428151741/2500000000 : ℝ)^4971 ≤ (5417635030767/50000000000000 : ℝ)^3947 := by
    have hnat : (428151741 : ℕ)^4971*50000000000000^3947 ≤ 5417635030767^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428151741 2500000000 5417635030767 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296199779/2500000000 : ℝ)^4971 ≤ (43724282045653/100000000000000 : ℝ)^3947 := by
    have hnat : (1296199779 : ℕ)^4971*100000000000000^3947 ≤ 43724282045653^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296199779 2500000000 43724282045653 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668217197/1250000000 : ℝ), (-428151741/2500000000 : ℝ), (1296199779/2500000000 : ℝ)] ![(2272022393651/5000000000000 : ℝ), (5417635030767/50000000000000 : ℝ), (43724282045653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668217197/1250000000 : ℝ)|^4971 ≤ (2272022393651/5000000000000 : ℝ)^3947
        have hw : |(668217197/1250000000 : ℝ)|=(668217197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428151741/2500000000 : ℝ)|^4971 ≤ (5417635030767/50000000000000 : ℝ)^3947
        have hw : |(-428151741/2500000000 : ℝ)|=(428151741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296199779/2500000000 : ℝ)|^4971 ≤ (43724282045653/100000000000000 : ℝ)^3947
        have hw : |(1296199779/2500000000 : ℝ)|=(1296199779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s4_2 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345737437/10000000000 : ℝ)*x 0 + (518479917/1000000000 : ℝ)*x 1 + (-42815177/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345737437/10000000000 : ℝ)^4971 ≤ (45440446384939/100000000000000 : ℝ)^3947 := by
    have hnat : (5345737437 : ℕ)^4971*100000000000000^3947 ≤ 45440446384939^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345737437 10000000000 45440446384939 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518479917/1000000000 : ℝ)^4971 ≤ (4372428261919/10000000000000 : ℝ)^3947 := by
    have hnat : (518479917 : ℕ)^4971*10000000000000^3947 ≤ 4372428261919^3947*1000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518479917 1000000000 4372428261919 10000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42815177/250000000 : ℝ)^4971 ≤ (5417635492921/50000000000000 : ℝ)^3947 := by
    have hnat : (42815177 : ℕ)^4971*50000000000000^3947 ≤ 5417635492921^3947*250000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42815177 250000000 5417635492921 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345737437/10000000000 : ℝ), (518479917/1000000000 : ℝ), (-42815177/250000000 : ℝ)] ![(45440446384939/100000000000000 : ℝ), (4372428261919/10000000000000 : ℝ), (5417635492921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345737437/10000000000 : ℝ)|^4971 ≤ (45440446384939/100000000000000 : ℝ)^3947
        have hw : |(5345737437/10000000000 : ℝ)|=(5345737437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518479917/1000000000 : ℝ)|^4971 ≤ (4372428261919/10000000000000 : ℝ)^3947
        have hw : |(518479917/1000000000 : ℝ)|=(518479917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42815177/250000000 : ℝ)|^4971 ≤ (5417635492921/50000000000000 : ℝ)^3947
        have hw : |(-42815177/250000000 : ℝ)|=(42815177/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s4_3 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4170891261/10000000000 : ℝ)*x 0 + (192024873/500000000 : ℝ)*x 1 + (2260520629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4170891261/10000000000 : ℝ)^4971 ≤ (33243135233383/100000000000000 : ℝ)^3947 := by
    have hnat : (4170891261 : ℕ)^4971*100000000000000^3947 ≤ 33243135233383^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170891261 10000000000 33243135233383 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192024873/500000000 : ℝ)^4971 ≤ (29961392218267/100000000000000 : ℝ)^3947 := by
    have hnat : (192024873 : ℕ)^4971*100000000000000^3947 ≤ 29961392218267^3947*500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192024873 500000000 29961392218267 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2260520629/5000000000 : ℝ)^4971 ≤ (9198868133673/25000000000000 : ℝ)^3947 := by
    have hnat : (2260520629 : ℕ)^4971*25000000000000^3947 ≤ 9198868133673^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260520629 5000000000 9198868133673 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4170891261/10000000000 : ℝ), (192024873/500000000 : ℝ), (2260520629/5000000000 : ℝ)] ![(33243135233383/100000000000000 : ℝ), (29961392218267/100000000000000 : ℝ), (9198868133673/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4170891261/10000000000 : ℝ)|^4971 ≤ (33243135233383/100000000000000 : ℝ)^3947
        have hw : |(4170891261/10000000000 : ℝ)|=(4170891261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192024873/500000000 : ℝ)|^4971 ≤ (29961392218267/100000000000000 : ℝ)^3947
        have hw : |(192024873/500000000 : ℝ)|=(192024873/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2260520629/5000000000 : ℝ)|^4971 ≤ (9198868133673/25000000000000 : ℝ)^3947
        have hw : |(2260520629/5000000000 : ℝ)|=(2260520629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s4_4 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1579515783/10000000000 : ℝ)*x 0 + (3241729/6250000 : ℝ)*x 1 + (2720802409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1579515783/10000000000 : ℝ)^4971 ≤ (4892839823833/50000000000000 : ℝ)^3947 := by
    have hnat : (1579515783 : ℕ)^4971*50000000000000^3947 ≤ 4892839823833^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1579515783 10000000000 4892839823833 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3241729/6250000 : ℝ)^4971 ≤ (21872588846317/50000000000000 : ℝ)^3947 := by
    have hnat : (3241729 : ℕ)^4971*50000000000000^3947 ≤ 21872588846317^3947*6250000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3241729 6250000 21872588846317 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720802409/5000000000 : ℝ)^4971 ≤ (23234571326019/50000000000000 : ℝ)^3947 := by
    have hnat : (2720802409 : ℕ)^4971*50000000000000^3947 ≤ 23234571326019^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720802409 5000000000 23234571326019 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1579515783/10000000000 : ℝ), (3241729/6250000 : ℝ), (2720802409/5000000000 : ℝ)] ![(4892839823833/50000000000000 : ℝ), (21872588846317/50000000000000 : ℝ), (23234571326019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1579515783/10000000000 : ℝ)|^4971 ≤ (4892839823833/50000000000000 : ℝ)^3947
        have hw : |(-1579515783/10000000000 : ℝ)|=(1579515783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3241729/6250000 : ℝ)|^4971 ≤ (21872588846317/50000000000000 : ℝ)^3947
        have hw : |(3241729/6250000 : ℝ)|=(3241729/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720802409/5000000000 : ℝ)|^4971 ≤ (23234571326019/50000000000000 : ℝ)^3947
        have hw : |(2720802409/5000000000 : ℝ)|=(2720802409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s4_5 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638250627/5000000000 : ℝ)*x 0 + (-363950263/2500000000 : ℝ)*x 1 + (2720802409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638250627/5000000000 : ℝ)^4971 ≤ (8940095959977/20000000000000 : ℝ)^3947 := by
    have hnat : (2638250627 : ℕ)^4971*20000000000000^3947 ≤ 8940095959977^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638250627 5000000000 8940095959977 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (363950263/2500000000 : ℝ)^4971 ≤ (1766075506533/20000000000000 : ℝ)^3947 := by
    have hnat : (363950263 : ℕ)^4971*20000000000000^3947 ≤ 1766075506533^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363950263 2500000000 1766075506533 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720802409/5000000000 : ℝ)^4971 ≤ (23234571326019/50000000000000 : ℝ)^3947 := by
    have hnat : (2720802409 : ℕ)^4971*50000000000000^3947 ≤ 23234571326019^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720802409 5000000000 23234571326019 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638250627/5000000000 : ℝ), (-363950263/2500000000 : ℝ), (2720802409/5000000000 : ℝ)] ![(8940095959977/20000000000000 : ℝ), (1766075506533/20000000000000 : ℝ), (23234571326019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638250627/5000000000 : ℝ)|^4971 ≤ (8940095959977/20000000000000 : ℝ)^3947
        have hw : |(2638250627/5000000000 : ℝ)|=(2638250627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-363950263/2500000000 : ℝ)|^4971 ≤ (1766075506533/20000000000000 : ℝ)^3947
        have hw : |(-363950263/2500000000 : ℝ)|=(363950263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720802409/5000000000 : ℝ)|^4971 ≤ (23234571326019/50000000000000 : ℝ)^3947
        have hw : |(2720802409/5000000000 : ℝ)|=(2720802409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s4_6 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638250627/5000000000 : ℝ)*x 0 + (2720802409/5000000000 : ℝ)*x 1 + (-363950263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638250627/5000000000 : ℝ)^4971 ≤ (8940095959977/20000000000000 : ℝ)^3947 := by
    have hnat : (2638250627 : ℕ)^4971*20000000000000^3947 ≤ 8940095959977^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638250627 5000000000 8940095959977 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720802409/5000000000 : ℝ)^4971 ≤ (23234571326019/50000000000000 : ℝ)^3947 := by
    have hnat : (2720802409 : ℕ)^4971*50000000000000^3947 ≤ 23234571326019^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720802409 5000000000 23234571326019 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (363950263/2500000000 : ℝ)^4971 ≤ (1766075506533/20000000000000 : ℝ)^3947 := by
    have hnat : (363950263 : ℕ)^4971*20000000000000^3947 ≤ 1766075506533^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363950263 2500000000 1766075506533 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638250627/5000000000 : ℝ), (2720802409/5000000000 : ℝ), (-363950263/2500000000 : ℝ)] ![(8940095959977/20000000000000 : ℝ), (23234571326019/50000000000000 : ℝ), (1766075506533/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638250627/5000000000 : ℝ)|^4971 ≤ (8940095959977/20000000000000 : ℝ)^3947
        have hw : |(2638250627/5000000000 : ℝ)|=(2638250627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720802409/5000000000 : ℝ)|^4971 ≤ (23234571326019/50000000000000 : ℝ)^3947
        have hw : |(2720802409/5000000000 : ℝ)|=(2720802409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-363950263/2500000000 : ℝ)|^4971 ≤ (1766075506533/20000000000000 : ℝ)^3947
        have hw : |(-363950263/2500000000 : ℝ)|=(363950263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_s4_7 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4171055099/10000000000 : ℝ)*x 0 + (4515867079/10000000000 : ℝ)*x 1 + (3845726227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4171055099/10000000000 : ℝ)^4971 ≤ (51944968527/156250000000 : ℝ)^3947 := by
    have hnat : (4171055099 : ℕ)^4971*156250000000^3947 ≤ 51944968527^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171055099 10000000000 51944968527 156250000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4515867079/10000000000 : ℝ)^4971 ≤ (36742444015201/100000000000000 : ℝ)^3947 := by
    have hnat : (4515867079 : ℕ)^4971*100000000000000^3947 ≤ 36742444015201^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515867079 10000000000 36742444015201 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3845726227/10000000000 : ℝ)^4971 ≤ (30012776122799/100000000000000 : ℝ)^3947 := by
    have hnat : (3845726227 : ℕ)^4971*100000000000000^3947 ≤ 30012776122799^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3845726227 10000000000 30012776122799 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4171055099/10000000000 : ℝ), (4515867079/10000000000 : ℝ), (3845726227/10000000000 : ℝ)] ![(51944968527/156250000000 : ℝ), (36742444015201/100000000000000 : ℝ), (30012776122799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4171055099/10000000000 : ℝ)|^4971 ≤ (51944968527/156250000000 : ℝ)^3947
        have hw : |(4171055099/10000000000 : ℝ)|=(4171055099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4515867079/10000000000 : ℝ)|^4971 ≤ (36742444015201/100000000000000 : ℝ)^3947
        have hw : |(4515867079/10000000000 : ℝ)|=(4515867079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3845726227/10000000000 : ℝ)|^4971 ≤ (30012776122799/100000000000000 : ℝ)^3947
        have hw : |(3845726227/10000000000 : ℝ)|=(3845726227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1663_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3249/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10733/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (671/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8121/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3249/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10733/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3249/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10733/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3249/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10733/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3249/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10733/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3249/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10733/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3249/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10733/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10733/100000 : ℝ) ^ (4967/1024 : ℝ) ≤ (497015060902731/25000000000000000000 : ℝ) := by
    have hpowers : (10733/100000 : ℝ)^4967 ≤ (497015060902731/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10733 : ℕ)^4967*25000000000000000000^1024 ≤ 497015060902731^1024*100000^4967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10733 100000 497015060902731 25000000000000000000 4967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10733/100000 : ℝ)) (X := (497015060902731/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3249/20000 : ℝ) ^ (4967/1024 : ℝ) ≤ (231925327296259/1562500000000000000 : ℝ) := by
    have hpowers : (3249/20000 : ℝ)^4967 ≤ (231925327296259/1562500000000000000 : ℝ)^1024 := by
      have hnat : (3249 : ℕ)^4967*1562500000000000000^1024 ≤ 231925327296259^1024*20000^4967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3249 20000 231925327296259 1562500000000000000 4967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3249/20000 : ℝ)) (X := (231925327296259/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500497015060902731/12500000000000000000 : ℝ) ≤ (125001024633361/125000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (12500497015060902731/12500000000000000000 : ℝ)^1024 ≤ (125001024633361/125000000000000 : ℝ)^4967 := by
      have hnat : (12500497015060902731 : ℕ)^1024*125000000000000^4967 ≤ 125001024633361^4967*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500497015060902731 12500000000000000000 125001024633361 125000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125001024633361/125000000000000 : ℝ)) (X := (12500497015060902731/12500000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (200033662562381143/200000000000000000 : ℝ) ≤ (500017348581263/500000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (200033662562381143/200000000000000000 : ℝ)^1024 ≤ (500017348581263/500000000000000 : ℝ)^4967 := by
      have hnat : (200033662562381143 : ℕ)^1024*500000000000000^4967 ≤ 500017348581263^4967*200000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200033662562381143 200000000000000000 500017348581263 500000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500017348581263/500000000000000 : ℝ)) (X := (200033662562381143/200000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (781481925327296259/781250000000000000 : ℝ) ≤ (250015299314541/250000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (781481925327296259/781250000000000000 : ℝ)^1024 ≤ (250015299314541/250000000000000 : ℝ)^4967 := by
      have hnat : (781481925327296259 : ℕ)^1024*250000000000000^4967 ≤ 250015299314541^4967*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781481925327296259 781250000000000000 250015299314541 250000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250015299314541/250000000000000 : ℝ)) (X := (781481925327296259/781250000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(497015060902731/25000000000000000000 : ℝ) ≤ ((1377869082794930337/1378000000000000000 : ℝ)+2*(13250047819/27560000000000 : ℝ)*(10733/100000 : ℝ))^(4967/1024 : ℝ) := by
    rw [show (1377869082794930337/1378000000000000000 : ℝ)+2*(13250047819/27560000000000 : ℝ)*(10733/100000 : ℝ)=(125001024633361/125000000000000 : ℝ) by norm_num, show 1+2*(497015060902731/25000000000000000000 : ℝ)=(12500497015060902731/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(231925327296259/1562500000000000000 : ℝ)+(497015060902731/25000000000000000000 : ℝ) ≤ ((1377869082794930337/1378000000000000000 : ℝ)+(13250047819/27560000000000 : ℝ)*((3249/20000 : ℝ)+(10733/100000 : ℝ)))^(4967/1024 : ℝ) := by
    rw [show (1377869082794930337/1378000000000000000 : ℝ)+(13250047819/27560000000000 : ℝ)*((3249/20000 : ℝ)+(10733/100000 : ℝ))=(500017348581263/500000000000000 : ℝ) by norm_num, show 1+(231925327296259/1562500000000000000 : ℝ)+(497015060902731/25000000000000000000 : ℝ)=(200033662562381143/200000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(231925327296259/1562500000000000000 : ℝ) ≤ ((1377869082794930337/1378000000000000000 : ℝ)+2*(13250047819/27560000000000 : ℝ)*(3249/20000 : ℝ))^(4967/1024 : ℝ) := by
    rw [show (1377869082794930337/1378000000000000000 : ℝ)+2*(13250047819/27560000000000 : ℝ)*(3249/20000 : ℝ)=(250015299314541/250000000000000 : ℝ) by norm_num, show 1+2*(231925327296259/1562500000000000000 : ℝ)=(781481925327296259/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1377869082794930337/1378000000000000000 : ℝ)*(X 1 0+X 2 0)+(13250047819/27560000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (10733/100000 : ℝ)) (hi := (3249/20000 : ℝ)) (c := (1377869082794930337/1378000000000000000 : ℝ)) (alpha := (13250047819/27560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1377869082794930337/1378000000000000000 : ℝ)*(X 0 1+X 2 1)+(13250047819/27560000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (10733/100000 : ℝ)) (hi := (3249/20000 : ℝ)) (c := (1377869082794930337/1378000000000000000 : ℝ)) (alpha := (13250047819/27560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1377869082794930337/1378000000000000000 : ℝ)*(X 0 2+X 1 2)+(13250047819/27560000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (10733/100000 : ℝ)) (hi := (3249/20000 : ℝ)) (c := (1377869082794930337/1378000000000000000 : ℝ)) (alpha := (13250047819/27560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-789726781/5000000000 : ℝ)*X 0 0+(2721796567/5000000000 : ℝ)*X 0 1+(51847987/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668217197/1250000000 : ℝ)*X 1 0+(-428151741/2500000000 : ℝ)*X 1 1+(1296199779/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345737437/10000000000 : ℝ)*X 2 0+(518479917/1000000000 : ℝ)*X 2 1+(-42815177/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4170891261/10000000000 : ℝ)*X 0 0+(192024873/500000000 : ℝ)*X 0 1+(2260520629/5000000000 : ℝ)*X 0 2+(4170891261/10000000000 : ℝ)*X 1 0+(192024873/500000000 : ℝ)*X 1 1+(2260520629/5000000000 : ℝ)*X 1 2+(4170891261/10000000000 : ℝ)*X 2 0+(192024873/500000000 : ℝ)*X 2 1+(2260520629/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1579515783/10000000000 : ℝ)*X 0 0+(3241729/6250000 : ℝ)*X 0 1+(2720802409/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638250627/5000000000 : ℝ)*X 1 0+(-363950263/2500000000 : ℝ)*X 1 1+(2720802409/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638250627/5000000000 : ℝ)*X 2 0+(2720802409/5000000000 : ℝ)*X 2 1+(-363950263/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4171055099/10000000000 : ℝ)*X 0 0+(4515867079/10000000000 : ℝ)*X 0 1+(3845726227/10000000000 : ℝ)*X 0 2+(4171055099/10000000000 : ℝ)*X 1 0+(4515867079/10000000000 : ℝ)*X 1 1+(3845726227/10000000000 : ℝ)*X 1 2+(4171055099/10000000000 : ℝ)*X 2 0+(4515867079/10000000000 : ℝ)*X 2 1+(3845726227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (194897624000090843386721301/34450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33902201/5000000000000 : ℝ)*(base19) + (573786167/100000000000000 : ℝ)*(base23) + (207559791/100000000000000 : ℝ)*(upper3) + (2022593/100000000000000 : ℝ)*(upper4) + (98090099/100000000000000 : ℝ)*(upper5) + (2666759051251391/100000000000000 : ℝ)*(major0) + (2666759051251391/100000000000000 : ℝ)*(major1) + (2666759051251391/100000000000000 : ℝ)*(major2) + (1932042280109417/50000000000000 : ℝ)*(sp0) + (3864094772818599/100000000000000 : ℝ)*(sp1) + (966023719269113/25000000000000 : ℝ)*(sp2) + (734708709924909/50000000000000 : ℝ)*(sp3) + (2178128757/20000000000000 : ℝ)*(sp4) + (5043210149/100000000000000 : ℝ)*(sp7) + (1469422463059967/100000000000000 : ℝ)*(f.failure) + (1932047725431309/50000000000000 : ℝ)*(f.sum) + (1233173686679/1378000000000000000000000000 : ℝ)*base66 + (816526804173801233/137800000000000000000000000000000 : ℝ)*base68 + (1243801057995801233/137800000000000000000000000000000 : ℝ)*base70 + (139232021411398767/137800000000000000000000000000000 : ℝ)*base71 + (754413924759/1378000000000000000000000000 : ℝ)*base73 + (2498757585137001233/137800000000000000000000000000000 : ℝ)*base76 + (475570602088601233/137800000000000000000000000000000 : ℝ)*base78 + (1870618958749001233/137800000000000000000000000000000 : ℝ)*base80 + (2373474227983/1378000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (42982547/5000000000000000000000 : ℝ)*base89 + (42982547/5000000000000000000000 : ℝ)*base91 + (42982547/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (313674788360498925843505827/34450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (165558037/12500000000000 : ℝ)*(base19) + (1431105059/100000000000000 : ℝ)*(base23) + (206481343/50000000000000 : ℝ)*(lower1) + (7631219/4000000000000 : ℝ)*(upper3) + (48052637/100000000000000 : ℝ)*(lower4) + (188424959/100000000000000 : ℝ)*(upper5) + (1354063919106257/50000000000000 : ℝ)*(major0) + (1354063919106257/50000000000000 : ℝ)*(major1) + (1354063919106257/50000000000000 : ℝ)*(major2) + (1854247/156250000000 : ℝ)*(sp2) + (3924038115254279/100000000000000 : ℝ)*(sp4) + (3924036790789983/100000000000000 : ℝ)*(sp5) + (196201774871557/5000000000000 : ℝ)*(sp6) + (373054314415859/25000000000000 : ℝ)*(sp7) + (373054314415859/25000000000000 : ℝ)*(f.failure) + (3924038115254279/100000000000000 : ℝ)*(f.sum) + (20638585759/17225000000000000000000000 : ℝ)*base65 + (408459307658368609/68900000000000000000000000000000 : ℝ)*base67 + (599678819376631391/68900000000000000000000000000000 : ℝ)*base70 + (5082824796300568609/68900000000000000000000000000000 : ℝ)*base71 + (2700129251509/689000000000000000000000000 : ℝ)*base74 + (4431719186357431391/68900000000000000000000000000000 : ℝ)*base76 + (460819033337631391/68900000000000000000000000000000 : ℝ)*base78 + (451536748169631391/68900000000000000000000000000000 : ℝ)*base80 + (533219765541/137800000000000000000000000 : ℝ)*base82 + (18670519/1250000000000000000000 : ℝ)*base89 + (18670519/1250000000000000000000 : ℝ)*base91 + (18670519/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1663_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3249/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10733/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8121/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1663_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1663_box_0 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-663021593/5000000000 : ℝ)*x 0 + (168902703/312500000 : ℝ)*x 1 + (5404886437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663021593/5000000000 : ℝ)^4971 ≤ (1962710248759/25000000000000 : ℝ)^3947 := by
    have hnat : (663021593 : ℕ)^4971*25000000000000^3947 ≤ 1962710248759^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663021593 5000000000 1962710248759 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168902703/312500000 : ℝ)^4971 ≤ (46074579811041/100000000000000 : ℝ)^3947 := by
    have hnat : (168902703 : ℕ)^4971*100000000000000^3947 ≤ 46074579811041^3947*312500000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168902703 312500000 46074579811041 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404886437/10000000000 : ℝ)^4971 ≤ (11518644794401/25000000000000 : ℝ)^3947 := by
    have hnat : (5404886437 : ℕ)^4971*25000000000000^3947 ≤ 11518644794401^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404886437 10000000000 11518644794401 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-663021593/5000000000 : ℝ), (168902703/312500000 : ℝ), (5404886437/10000000000 : ℝ)] ![(1962710248759/25000000000000 : ℝ), (46074579811041/100000000000000 : ℝ), (11518644794401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-663021593/5000000000 : ℝ)|^4971 ≤ (1962710248759/25000000000000 : ℝ)^3947
        have hw : |(-663021593/5000000000 : ℝ)|=(663021593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168902703/312500000 : ℝ)|^4971 ≤ (46074579811041/100000000000000 : ℝ)^3947
        have hw : |(168902703/312500000 : ℝ)|=(168902703/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404886437/10000000000 : ℝ)|^4971 ≤ (11518644794401/25000000000000 : ℝ)^3947
        have hw : |(5404886437/10000000000 : ℝ)|=(5404886437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_1 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625425007/5000000000 : ℝ)*x 0 + (-1542591987/10000000000 : ℝ)*x 1 + (270244319/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625425007/5000000000 : ℝ)^4971 ≤ (44426967506707/100000000000000 : ℝ)^3947 := by
    have hnat : (2625425007 : ℕ)^4971*100000000000000^3947 ≤ 44426967506707^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625425007 5000000000 44426967506707 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1542591987/10000000000 : ℝ)^4971 ≤ (2374613477893/25000000000000 : ℝ)^3947 := by
    have hnat : (1542591987 : ℕ)^4971*25000000000000^3947 ≤ 2374613477893^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542591987 10000000000 2374613477893 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270244319/500000000 : ℝ)^4971 ≤ (1151864464141/2500000000000 : ℝ)^3947 := by
    have hnat : (270244319 : ℕ)^4971*2500000000000^3947 ≤ 1151864464141^3947*500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270244319 500000000 1151864464141 2500000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625425007/5000000000 : ℝ), (-1542591987/10000000000 : ℝ), (270244319/500000000 : ℝ)] ![(44426967506707/100000000000000 : ℝ), (2374613477893/25000000000000 : ℝ), (1151864464141/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625425007/5000000000 : ℝ)|^4971 ≤ (44426967506707/100000000000000 : ℝ)^3947
        have hw : |(2625425007/5000000000 : ℝ)|=(2625425007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1542591987/10000000000 : ℝ)|^4971 ≤ (2374613477893/25000000000000 : ℝ)^3947
        have hw : |(-1542591987/10000000000 : ℝ)|=(1542591987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270244319/500000000 : ℝ)|^4971 ≤ (1151864464141/2500000000000 : ℝ)^3947
        have hw : |(270244319/500000000 : ℝ)|=(270244319/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_2 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625425033/5000000000 : ℝ)*x 0 + (1351221599/2500000000 : ℝ)*x 1 + (-1542591893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625425033/5000000000 : ℝ)^4971 ≤ (22213484030409/50000000000000 : ℝ)^3947 := by
    have hnat : (2625425033 : ℕ)^4971*50000000000000^3947 ≤ 22213484030409^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625425033 5000000000 22213484030409 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351221599/2500000000 : ℝ)^4971 ≤ (46074578737419/100000000000000 : ℝ)^3947 := by
    have hnat : (1351221599 : ℕ)^4971*100000000000000^3947 ≤ 46074578737419^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351221599 2500000000 46074578737419 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1542591893/10000000000 : ℝ)^4971 ≤ (9498453182607/100000000000000 : ℝ)^3947 := by
    have hnat : (1542591893 : ℕ)^4971*100000000000000^3947 ≤ 9498453182607^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542591893 10000000000 9498453182607 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625425033/5000000000 : ℝ), (1351221599/2500000000 : ℝ), (-1542591893/10000000000 : ℝ)] ![(22213484030409/50000000000000 : ℝ), (46074578737419/100000000000000 : ℝ), (9498453182607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625425033/5000000000 : ℝ)|^4971 ≤ (22213484030409/50000000000000 : ℝ)^3947
        have hw : |(2625425033/5000000000 : ℝ)|=(2625425033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351221599/2500000000 : ℝ)|^4971 ≤ (46074578737419/100000000000000 : ℝ)^3947
        have hw : |(1351221599/2500000000 : ℝ)|=(1351221599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1542591893/10000000000 : ℝ)|^4971 ≤ (9498453182607/100000000000000 : ℝ)^3947
        have hw : |(-1542591893/10000000000 : ℝ)|=(1542591893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_3 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2223432187/5000000000 : ℝ)*x 0 + (2022359373/5000000000 : ℝ)*x 1 + (2022359353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2223432187/5000000000 : ℝ)^4971 ≤ (36036769075983/100000000000000 : ℝ)^3947 := by
    have hnat : (2223432187 : ℕ)^4971*100000000000000^3947 ≤ 36036769075983^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223432187 5000000000 36036769075983 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2022359373/5000000000 : ℝ)^4971 ≤ (7995403913273/25000000000000 : ℝ)^3947 := by
    have hnat : (2022359373 : ℕ)^4971*25000000000000^3947 ≤ 7995403913273^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022359373 5000000000 7995403913273 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2022359353/5000000000 : ℝ)^4971 ≤ (31981615254757/100000000000000 : ℝ)^3947 := by
    have hnat : (2022359353 : ℕ)^4971*100000000000000^3947 ≤ 31981615254757^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022359353 5000000000 31981615254757 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2223432187/5000000000 : ℝ), (2022359373/5000000000 : ℝ), (2022359353/5000000000 : ℝ)] ![(36036769075983/100000000000000 : ℝ), (7995403913273/25000000000000 : ℝ), (31981615254757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2223432187/5000000000 : ℝ)|^4971 ≤ (36036769075983/100000000000000 : ℝ)^3947
        have hw : |(2223432187/5000000000 : ℝ)|=(2223432187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2022359373/5000000000 : ℝ)|^4971 ≤ (7995403913273/25000000000000 : ℝ)^3947
        have hw : |(2022359373/5000000000 : ℝ)|=(2022359373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2022359353/5000000000 : ℝ)|^4971 ≤ (31981615254757/100000000000000 : ℝ)^3947
        have hw : |(2022359353/5000000000 : ℝ)|=(2022359353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_4 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-57606727/312500000 : ℝ)*x 0 + (5216020611/10000000000 : ℝ)*x 1 + (5216020333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57606727/312500000 : ℝ)^4971 ≤ (1485963941517/12500000000000 : ℝ)^3947 := by
    have hnat : (57606727 : ℕ)^4971*12500000000000^3947 ≤ 1485963941517^3947*312500000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57606727 312500000 1485963941517 12500000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216020611/10000000000 : ℝ)^4971 ≤ (2753509106229/6250000000000 : ℝ)^3947 := by
    have hnat : (5216020611 : ℕ)^4971*6250000000000^3947 ≤ 2753509106229^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216020611 10000000000 2753509106229 6250000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216020333/10000000000 : ℝ)^4971 ≤ (4405614274241/10000000000000 : ℝ)^3947 := by
    have hnat : (5216020333 : ℕ)^4971*10000000000000^3947 ≤ 4405614274241^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216020333 10000000000 4405614274241 10000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-57606727/312500000 : ℝ), (5216020611/10000000000 : ℝ), (5216020333/10000000000 : ℝ)] ![(1485963941517/12500000000000 : ℝ), (2753509106229/6250000000000 : ℝ), (4405614274241/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-57606727/312500000 : ℝ)|^4971 ≤ (1485963941517/12500000000000 : ℝ)^3947
        have hw : |(-57606727/312500000 : ℝ)|=(57606727/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216020611/10000000000 : ℝ)|^4971 ≤ (2753509106229/6250000000000 : ℝ)^3947
        have hw : |(5216020611/10000000000 : ℝ)|=(5216020611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216020333/10000000000 : ℝ)|^4971 ≤ (4405614274241/10000000000000 : ℝ)^3947
        have hw : |(5216020333/10000000000 : ℝ)|=(5216020333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_5 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076051843/2000000000 : ℝ)*x 0 + (-1623934677/10000000000 : ℝ)*x 1 + (5216020643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076051843/2000000000 : ℝ)^4971 ≤ (45810332335191/100000000000000 : ℝ)^3947 := by
    have hnat : (1076051843 : ℕ)^4971*100000000000000^3947 ≤ 45810332335191^3947*2000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076051843 2000000000 45810332335191 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1623934677/10000000000 : ℝ)^4971 ≤ (5066760803729/50000000000000 : ℝ)^3947 := by
    have hnat : (1623934677 : ℕ)^4971*50000000000000^3947 ≤ 5066760803729^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1623934677 10000000000 5066760803729 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216020643/10000000000 : ℝ)^4971 ≤ (11014036510017/25000000000000 : ℝ)^3947 := by
    have hnat : (5216020643 : ℕ)^4971*25000000000000^3947 ≤ 11014036510017^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216020643 10000000000 11014036510017 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076051843/2000000000 : ℝ), (-1623934677/10000000000 : ℝ), (5216020643/10000000000 : ℝ)] ![(45810332335191/100000000000000 : ℝ), (5066760803729/50000000000000 : ℝ), (11014036510017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076051843/2000000000 : ℝ)|^4971 ≤ (45810332335191/100000000000000 : ℝ)^3947
        have hw : |(1076051843/2000000000 : ℝ)|=(1076051843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1623934677/10000000000 : ℝ)|^4971 ≤ (5066760803729/50000000000000 : ℝ)^3947
        have hw : |(-1623934677/10000000000 : ℝ)|=(1623934677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216020643/10000000000 : ℝ)|^4971 ≤ (11014036510017/25000000000000 : ℝ)^3947
        have hw : |(5216020643/10000000000 : ℝ)|=(5216020643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_6 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690129813/5000000000 : ℝ)*x 0 + (104320403/200000000 : ℝ)*x 1 + (-1623934783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690129813/5000000000 : ℝ)^4971 ≤ (45810336742553/100000000000000 : ℝ)^3947 := by
    have hnat : (2690129813 : ℕ)^4971*100000000000000^3947 ≤ 45810336742553^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690129813 5000000000 45810336742553 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104320403/200000000 : ℝ)^4971 ≤ (44056140795729/100000000000000 : ℝ)^3947 := by
    have hnat : (104320403 : ℕ)^4971*100000000000000^3947 ≤ 44056140795729^3947*200000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104320403 200000000 44056140795729 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1623934783/10000000000 : ℝ)^4971 ≤ (5066761220257/50000000000000 : ℝ)^3947 := by
    have hnat : (1623934783 : ℕ)^4971*50000000000000^3947 ≤ 5066761220257^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1623934783 10000000000 5066761220257 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690129813/5000000000 : ℝ), (104320403/200000000 : ℝ), (-1623934783/10000000000 : ℝ)] ![(45810336742553/100000000000000 : ℝ), (44056140795729/100000000000000 : ℝ), (5066761220257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690129813/5000000000 : ℝ)|^4971 ≤ (45810336742553/100000000000000 : ℝ)^3947
        have hw : |(2690129813/5000000000 : ℝ)|=(2690129813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104320403/200000000 : ℝ)|^4971 ≤ (44056140795729/100000000000000 : ℝ)^3947
        have hw : |(104320403/200000000 : ℝ)|=(104320403/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1623934783/10000000000 : ℝ)|^4971 ≤ (5066761220257/50000000000000 : ℝ)^3947
        have hw : |(-1623934783/10000000000 : ℝ)|=(1623934783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_7 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (972051529/2500000000 : ℝ)*x 0 + (1080932043/2500000000 : ℝ)*x 1 + (2161864061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (972051529/2500000000 : ℝ)^4971 ≤ (24344722313/80000000000 : ℝ)^3947 := by
    have hnat : (972051529 : ℕ)^4971*80000000000^3947 ≤ 24344722313^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972051529 2500000000 24344722313 80000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080932043/2500000000 : ℝ)^4971 ≤ (8696137199371/25000000000000 : ℝ)^3947 := by
    have hnat : (1080932043 : ℕ)^4971*25000000000000^3947 ≤ 8696137199371^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080932043 2500000000 8696137199371 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161864061/5000000000 : ℝ)^4971 ≤ (34784548290873/100000000000000 : ℝ)^3947 := by
    have hnat : (2161864061 : ℕ)^4971*100000000000000^3947 ≤ 34784548290873^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161864061 5000000000 34784548290873 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(972051529/2500000000 : ℝ), (1080932043/2500000000 : ℝ), (2161864061/5000000000 : ℝ)] ![(24344722313/80000000000 : ℝ), (8696137199371/25000000000000 : ℝ), (34784548290873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(972051529/2500000000 : ℝ)|^4971 ≤ (24344722313/80000000000 : ℝ)^3947
        have hw : |(972051529/2500000000 : ℝ)|=(972051529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080932043/2500000000 : ℝ)|^4971 ≤ (8696137199371/25000000000000 : ℝ)^3947
        have hw : |(1080932043/2500000000 : ℝ)|=(1080932043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2161864061/5000000000 : ℝ)|^4971 ≤ (34784548290873/100000000000000 : ℝ)^3947
        have hw : |(2161864061/5000000000 : ℝ)|=(2161864061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_8 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1732957369/10000000000 : ℝ)*x 0 + (1269973229/2500000000 : ℝ)*x 1 + (339636341/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1732957369/10000000000 : ℝ)^4971 ≤ (10997674796831/100000000000000 : ℝ)^3947 := by
    have hnat : (1732957369 : ℕ)^4971*100000000000000^3947 ≤ 10997674796831^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732957369 10000000000 10997674796831 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269973229/2500000000 : ℝ)^4971 ≤ (8522601475317/20000000000000 : ℝ)^3947 := by
    have hnat : (1269973229 : ℕ)^4971*20000000000000^3947 ≤ 8522601475317^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269973229 2500000000 8522601475317 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339636341/625000000 : ℝ)^4971 ≤ (46389317813043/100000000000000 : ℝ)^3947 := by
    have hnat : (339636341 : ℕ)^4971*100000000000000^3947 ≤ 46389317813043^3947*625000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339636341 625000000 46389317813043 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1732957369/10000000000 : ℝ), (1269973229/2500000000 : ℝ), (339636341/625000000 : ℝ)] ![(10997674796831/100000000000000 : ℝ), (8522601475317/20000000000000 : ℝ), (46389317813043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1732957369/10000000000 : ℝ)|^4971 ≤ (10997674796831/100000000000000 : ℝ)^3947
        have hw : |(-1732957369/10000000000 : ℝ)|=(1732957369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1269973229/2500000000 : ℝ)|^4971 ≤ (8522601475317/20000000000000 : ℝ)^3947
        have hw : |(1269973229/2500000000 : ℝ)|=(1269973229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339636341/625000000 : ℝ)|^4971 ≤ (46389317813043/100000000000000 : ℝ)^3947
        have hw : |(339636341/625000000 : ℝ)|=(339636341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_9 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230780063/10000000000 : ℝ)*x 0 + (-1529556353/10000000000 : ℝ)*x 1 + (5434181389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230780063/10000000000 : ℝ)^4971 ≤ (22106604250857/50000000000000 : ℝ)^3947 := by
    have hnat : (5230780063 : ℕ)^4971*50000000000000^3947 ≤ 22106604250857^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230780063 10000000000 22106604250857 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1529556353/10000000000 : ℝ)^4971 ≤ (4698737193967/50000000000000 : ℝ)^3947 := by
    have hnat : (1529556353 : ℕ)^4971*50000000000000^3947 ≤ 4698737193967^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529556353 10000000000 4698737193967 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434181389/10000000000 : ℝ)^4971 ≤ (46389317092707/100000000000000 : ℝ)^3947 := by
    have hnat : (5434181389 : ℕ)^4971*100000000000000^3947 ≤ 46389317092707^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434181389 10000000000 46389317092707 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230780063/10000000000 : ℝ), (-1529556353/10000000000 : ℝ), (5434181389/10000000000 : ℝ)] ![(22106604250857/50000000000000 : ℝ), (4698737193967/50000000000000 : ℝ), (46389317092707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230780063/10000000000 : ℝ)|^4971 ≤ (22106604250857/50000000000000 : ℝ)^3947
        have hw : |(5230780063/10000000000 : ℝ)|=(5230780063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1529556353/10000000000 : ℝ)|^4971 ≤ (4698737193967/50000000000000 : ℝ)^3947
        have hw : |(-1529556353/10000000000 : ℝ)|=(1529556353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434181389/10000000000 : ℝ)|^4971 ≤ (46389317092707/100000000000000 : ℝ)^3947
        have hw : |(5434181389/10000000000 : ℝ)|=(5434181389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_10 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230780597/10000000000 : ℝ)*x 0 + (2717090493/5000000000 : ℝ)*x 1 + (-764778089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230780597/10000000000 : ℝ)^4971 ≤ (44213214186361/100000000000000 : ℝ)^3947 := by
    have hnat : (5230780597 : ℕ)^4971*100000000000000^3947 ≤ 44213214186361^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230780597 10000000000 44213214186361 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717090493/5000000000 : ℝ)^4971 ≤ (23194656379969/50000000000000 : ℝ)^3947 := by
    have hnat : (2717090493 : ℕ)^4971*50000000000000^3947 ≤ 23194656379969^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717090493 5000000000 23194656379969 50000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (764778089/5000000000 : ℝ)^4971 ≤ (2349368258451/25000000000000 : ℝ)^3947 := by
    have hnat : (764778089 : ℕ)^4971*25000000000000^3947 ≤ 2349368258451^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764778089 5000000000 2349368258451 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230780597/10000000000 : ℝ), (2717090493/5000000000 : ℝ), (-764778089/5000000000 : ℝ)] ![(44213214186361/100000000000000 : ℝ), (23194656379969/50000000000000 : ℝ), (2349368258451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230780597/10000000000 : ℝ)|^4971 ≤ (44213214186361/100000000000000 : ℝ)^3947
        have hw : |(5230780597/10000000000 : ℝ)|=(5230780597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717090493/5000000000 : ℝ)|^4971 ≤ (23194656379969/50000000000000 : ℝ)^3947
        have hw : |(2717090493/5000000000 : ℝ)|=(2717090493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-764778089/5000000000 : ℝ)|^4971 ≤ (2349368258451/25000000000000 : ℝ)^3947
        have hw : |(-764778089/5000000000 : ℝ)|=(764778089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_11 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2265572771/5000000000 : ℝ)*x 0 + (1000340713/2500000000 : ℝ)*x 1 + (1000340719/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2265572771/5000000000 : ℝ)^4971 ≤ (9224768381801/25000000000000 : ℝ)^3947 := by
    have hnat : (2265572771 : ℕ)^4971*25000000000000^3947 ≤ 9224768381801^3947*5000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265572771 5000000000 9224768381801 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000340713/2500000000 : ℝ)^4971 ≤ (31550463110353/100000000000000 : ℝ)^3947 := by
    have hnat : (1000340713 : ℕ)^4971*100000000000000^3947 ≤ 31550463110353^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000340713 2500000000 31550463110353 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000340719/2500000000 : ℝ)^4971 ≤ (31550463348687/100000000000000 : ℝ)^3947 := by
    have hnat : (1000340719 : ℕ)^4971*100000000000000^3947 ≤ 31550463348687^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000340719 2500000000 31550463348687 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2265572771/5000000000 : ℝ), (1000340713/2500000000 : ℝ), (1000340719/2500000000 : ℝ)] ![(9224768381801/25000000000000 : ℝ), (31550463110353/100000000000000 : ℝ), (31550463348687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2265572771/5000000000 : ℝ)|^4971 ≤ (9224768381801/25000000000000 : ℝ)^3947
        have hw : |(2265572771/5000000000 : ℝ)|=(2265572771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1000340713/2500000000 : ℝ)|^4971 ≤ (31550463110353/100000000000000 : ℝ)^3947
        have hw : |(1000340713/2500000000 : ℝ)|=(1000340713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1000340719/2500000000 : ℝ)|^4971 ≤ (31550463348687/100000000000000 : ℝ)^3947
        have hw : |(1000340719/2500000000 : ℝ)|=(1000340719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_12 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1434584047/10000000000 : ℝ)*x 0 + (345994159/625000000 : ℝ)*x 1 + (5196233417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1434584047/10000000000 : ℝ)^4971 ≤ (8668601882603/100000000000000 : ℝ)^3947 := by
    have hnat : (1434584047 : ℕ)^4971*100000000000000^3947 ≤ 8668601882603^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1434584047 10000000000 8668601882603 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345994159/625000000 : ℝ)^4971 ≤ (5935704634197/12500000000000 : ℝ)^3947 := by
    have hnat : (345994159 : ℕ)^4971*12500000000000^3947 ≤ 5935704634197^3947*625000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345994159 625000000 5935704634197 12500000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196233417/10000000000 : ℝ)^4971 ≤ (43845761033737/100000000000000 : ℝ)^3947 := by
    have hnat : (5196233417 : ℕ)^4971*100000000000000^3947 ≤ 43845761033737^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196233417 10000000000 43845761033737 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1434584047/10000000000 : ℝ), (345994159/625000000 : ℝ), (5196233417/10000000000 : ℝ)] ![(8668601882603/100000000000000 : ℝ), (5935704634197/12500000000000 : ℝ), (43845761033737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1434584047/10000000000 : ℝ)|^4971 ≤ (8668601882603/100000000000000 : ℝ)^3947
        have hw : |(-1434584047/10000000000 : ℝ)|=(1434584047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(345994159/625000000 : ℝ)|^4971 ≤ (5935704634197/12500000000000 : ℝ)^3947
        have hw : |(345994159/625000000 : ℝ)|=(345994159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196233417/10000000000 : ℝ)|^4971 ≤ (43845761033737/100000000000000 : ℝ)^3947
        have hw : |(5196233417/10000000000 : ℝ)|=(5196233417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_13 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393828191/10000000000 : ℝ)*x 0 + (-408044723/2500000000 : ℝ)*x 1 + (324764567/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393828191/10000000000 : ℝ)^4971 ≤ (5744485866319/12500000000000 : ℝ)^3947 := by
    have hnat : (5393828191 : ℕ)^4971*12500000000000^3947 ≤ 5744485866319^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393828191 10000000000 5744485866319 12500000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408044723/2500000000 : ℝ)^4971 ≤ (10198355685253/100000000000000 : ℝ)^3947 := by
    have hnat : (408044723 : ℕ)^4971*100000000000000^3947 ≤ 10198355685253^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408044723 2500000000 10198355685253 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324764567/625000000 : ℝ)^4971 ≤ (2192287868369/5000000000000 : ℝ)^3947 := by
    have hnat : (324764567 : ℕ)^4971*5000000000000^3947 ≤ 2192287868369^3947*625000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324764567 625000000 2192287868369 5000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393828191/10000000000 : ℝ), (-408044723/2500000000 : ℝ), (324764567/625000000 : ℝ)] ![(5744485866319/12500000000000 : ℝ), (10198355685253/100000000000000 : ℝ), (2192287868369/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393828191/10000000000 : ℝ)|^4971 ≤ (5744485866319/12500000000000 : ℝ)^3947
        have hw : |(5393828191/10000000000 : ℝ)|=(5393828191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408044723/2500000000 : ℝ)|^4971 ≤ (10198355685253/100000000000000 : ℝ)^3947
        have hw : |(-408044723/2500000000 : ℝ)|=(408044723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(324764567/625000000 : ℝ)|^4971 ≤ (2192287868369/5000000000000 : ℝ)^3947
        have hw : |(324764567/625000000 : ℝ)|=(324764567/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_14 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393827993/10000000000 : ℝ)*x 0 + (5196233053/10000000000 : ℝ)*x 1 + (-1632179189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393827993/10000000000 : ℝ)^4971 ≤ (4595588480591/10000000000000 : ℝ)^3947 := by
    have hnat : (5393827993 : ℕ)^4971*10000000000000^3947 ≤ 4595588480591^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393827993 10000000000 4595588480591 10000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196233053/10000000000 : ℝ)^4971 ≤ (8769151433093/20000000000000 : ℝ)^3947 := by
    have hnat : (5196233053 : ℕ)^4971*20000000000000^3947 ≤ 8769151433093^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196233053 10000000000 8769151433093 20000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1632179189/10000000000 : ℝ)^4971 ≤ (10198358022451/100000000000000 : ℝ)^3947 := by
    have hnat : (1632179189 : ℕ)^4971*100000000000000^3947 ≤ 10198358022451^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1632179189 10000000000 10198358022451 100000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393827993/10000000000 : ℝ), (5196233053/10000000000 : ℝ), (-1632179189/10000000000 : ℝ)] ![(4595588480591/10000000000000 : ℝ), (8769151433093/20000000000000 : ℝ), (10198358022451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393827993/10000000000 : ℝ)|^4971 ≤ (4595588480591/10000000000000 : ℝ)^3947
        have hw : |(5393827993/10000000000 : ℝ)|=(5393827993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196233053/10000000000 : ℝ)|^4971 ≤ (8769151433093/20000000000000 : ℝ)^3947
        have hw : |(5196233053/10000000000 : ℝ)|=(5196233053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1632179189/10000000000 : ℝ)|^4971 ≤ (10198358022451/100000000000000 : ℝ)^3947
        have hw : |(-1632179189/10000000000 : ℝ)|=(1632179189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1663_box_15 (p : ℝ) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (957011701/2500000000 : ℝ)*x 0 + (4352906171/10000000000 : ℝ)*x 1 + (4352906077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (957011701/2500000000 : ℝ)^4971 ≤ (233118052931/781250000000 : ℝ)^3947 := by
    have hnat : (957011701 : ℕ)^4971*781250000000^3947 ≤ 233118052931^3947*2500000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957011701 2500000000 233118052931 781250000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4352906171/10000000000 : ℝ)^4971 ≤ (4385055635263/12500000000000 : ℝ)^3947 := by
    have hnat : (4352906171 : ℕ)^4971*12500000000000^3947 ≤ 4385055635263^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352906171 10000000000 4385055635263 12500000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4352906077/10000000000 : ℝ)^4971 ≤ (8770111032003/25000000000000 : ℝ)^3947 := by
    have hnat : (4352906077 : ℕ)^4971*25000000000000^3947 ≤ 8770111032003^3947*10000000000^4971 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352906077 10000000000 8770111032003 25000000000000 4971 3947 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4971/1024 : ℝ)) 4971 3947 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(957011701/2500000000 : ℝ), (4352906171/10000000000 : ℝ), (4352906077/10000000000 : ℝ)] ![(233118052931/781250000000 : ℝ), (4385055635263/12500000000000 : ℝ), (8770111032003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(957011701/2500000000 : ℝ)|^4971 ≤ (233118052931/781250000000 : ℝ)^3947
        have hw : |(957011701/2500000000 : ℝ)|=(957011701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4352906171/10000000000 : ℝ)|^4971 ≤ (4385055635263/12500000000000 : ℝ)^3947
        have hw : |(4352906171/10000000000 : ℝ)|=(4352906171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4352906077/10000000000 : ℝ)|^4971 ≤ (8770111032003/25000000000000 : ℝ)^3947
        have hw : |(4352906077/10000000000 : ℝ)|=(4352906077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1663_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(65123/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29383/50000 : ℝ) ∧ (8143/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88349/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (671/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (671/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (671/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (671/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (671/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (671/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (671/6250 : ℝ) ^ (4967/1024 : ℝ) ≤ (1990757098511153/100000000000000000000 : ℝ) := by
    have hpowers : (671/6250 : ℝ)^4967 ≤ (1990757098511153/100000000000000000000 : ℝ)^1024 := by
      have hnat : (671 : ℕ)^4967*100000000000000000000^1024 ≤ 1990757098511153^1024*6250^4967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        671 6250 1990757098511153 100000000000000000000 4967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (671/6250 : ℝ)) (X := (1990757098511153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8121/50000 : ℝ) ^ (4967/1024 : ℝ) ≤ (3707482396277607/25000000000000000000 : ℝ) := by
    have hpowers : (8121/50000 : ℝ)^4967 ≤ (3707482396277607/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8121 : ℕ)^4967*25000000000000000000^1024 ≤ 3707482396277607^1024*50000^4967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8121 50000 3707482396277607 25000000000000000000 4967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8121/50000 : ℝ)) (X := (3707482396277607/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001990757098511153/50000000000000000000 : ℝ) ≤ (5000041040931223/5000000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (50001990757098511153/50000000000000000000 : ℝ)^1024 ≤ (5000041040931223/5000000000000000 : ℝ)^4967 := by
      have hnat : (50001990757098511153 : ℕ)^1024*5000000000000000^4967 ≤ 5000041040931223^4967*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001990757098511153 50000000000000000000 5000041040931223 5000000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000041040931223/5000000000000000 : ℝ)) (X := (50001990757098511153/50000000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016820686683621581/100000000000000000000 : ℝ) ≤ (80002774025899/80000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (100016820686683621581/100000000000000000000 : ℝ)^1024 ≤ (80002774025899/80000000000000 : ℝ)^4967 := by
      have hnat : (100016820686683621581 : ℕ)^1024*80000000000000^4967 ≤ 80002774025899^4967*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016820686683621581 100000000000000000000 80002774025899 80000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80002774025899/80000000000000 : ℝ)) (X := (100016820686683621581/100000000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503707482396277607/12500000000000000000 : ℝ) ≤ (625038214038269/625000000000000 : ℝ) ^ (4967/1024 : ℝ) := by
    have hpowers : (12503707482396277607/12500000000000000000 : ℝ)^1024 ≤ (625038214038269/625000000000000 : ℝ)^4967 := by
      have hnat : (12503707482396277607 : ℕ)^1024*625000000000000^4967 ≤ 625038214038269^4967*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503707482396277607 12500000000000000000 625038214038269 625000000000000 1024 4967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625038214038269/625000000000000 : ℝ)) (X := (12503707482396277607/12500000000000000000 : ℝ)) (by norm_num) 4967 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1990757098511153/100000000000000000000 : ℝ) ≤ ((13763692229743038047/13765000000000000000 : ℝ)+2*(264671374929/550600000000000 : ℝ)*(671/6250 : ℝ))^(4967/1024 : ℝ) := by
    rw [show (13763692229743038047/13765000000000000000 : ℝ)+2*(264671374929/550600000000000 : ℝ)*(671/6250 : ℝ)=(5000041040931223/5000000000000000 : ℝ) by norm_num, show 1+2*(1990757098511153/100000000000000000000 : ℝ)=(50001990757098511153/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3707482396277607/25000000000000000000 : ℝ)+(1990757098511153/100000000000000000000 : ℝ) ≤ ((13763692229743038047/13765000000000000000 : ℝ)+(264671374929/550600000000000 : ℝ)*((8121/50000 : ℝ)+(671/6250 : ℝ)))^(4967/1024 : ℝ) := by
    rw [show (13763692229743038047/13765000000000000000 : ℝ)+(264671374929/550600000000000 : ℝ)*((8121/50000 : ℝ)+(671/6250 : ℝ))=(80002774025899/80000000000000 : ℝ) by norm_num, show 1+(3707482396277607/25000000000000000000 : ℝ)+(1990757098511153/100000000000000000000 : ℝ)=(100016820686683621581/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3707482396277607/25000000000000000000 : ℝ) ≤ ((13763692229743038047/13765000000000000000 : ℝ)+2*(264671374929/550600000000000 : ℝ)*(8121/50000 : ℝ))^(4967/1024 : ℝ) := by
    rw [show (13763692229743038047/13765000000000000000 : ℝ)+2*(264671374929/550600000000000 : ℝ)*(8121/50000 : ℝ)=(625038214038269/625000000000000 : ℝ) by norm_num, show 1+2*(3707482396277607/25000000000000000000 : ℝ)=(12503707482396277607/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13763692229743038047/13765000000000000000 : ℝ)*(X 1 0+X 2 0)+(264671374929/550600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (671/6250 : ℝ)) (hi := (8121/50000 : ℝ)) (c := (13763692229743038047/13765000000000000000 : ℝ)) (alpha := (264671374929/550600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13763692229743038047/13765000000000000000 : ℝ)*(X 0 1+X 2 1)+(264671374929/550600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (671/6250 : ℝ)) (hi := (8121/50000 : ℝ)) (c := (13763692229743038047/13765000000000000000 : ℝ)) (alpha := (264671374929/550600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13763692229743038047/13765000000000000000 : ℝ)*(X 0 2+X 1 2)+(264671374929/550600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4967/1024 : ℝ)) (lo := (671/6250 : ℝ)) (hi := (8121/50000 : ℝ)) (c := (13763692229743038047/13765000000000000000 : ℝ)) (alpha := (264671374929/550600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-663021593/5000000000 : ℝ)*X 0 0+(168902703/312500000 : ℝ)*X 0 1+(5404886437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2625425007/5000000000 : ℝ)*X 1 0+(-1542591987/10000000000 : ℝ)*X 1 1+(270244319/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2625425033/5000000000 : ℝ)*X 2 0+(1351221599/2500000000 : ℝ)*X 2 1+(-1542591893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2223432187/5000000000 : ℝ)*X 0 0+(2022359373/5000000000 : ℝ)*X 0 1+(2022359353/5000000000 : ℝ)*X 0 2+(2223432187/5000000000 : ℝ)*X 1 0+(2022359373/5000000000 : ℝ)*X 1 1+(2022359353/5000000000 : ℝ)*X 1 2+(2223432187/5000000000 : ℝ)*X 2 0+(2022359373/5000000000 : ℝ)*X 2 1+(2022359353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-57606727/312500000 : ℝ)*X 0 0+(5216020611/10000000000 : ℝ)*X 0 1+(5216020333/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1076051843/2000000000 : ℝ)*X 1 0+(-1623934677/10000000000 : ℝ)*X 1 1+(5216020643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2690129813/5000000000 : ℝ)*X 2 0+(104320403/200000000 : ℝ)*X 2 1+(-1623934783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((972051529/2500000000 : ℝ)*X 0 0+(1080932043/2500000000 : ℝ)*X 0 1+(2161864061/5000000000 : ℝ)*X 0 2+(972051529/2500000000 : ℝ)*X 1 0+(1080932043/2500000000 : ℝ)*X 1 1+(2161864061/5000000000 : ℝ)*X 1 2+(972051529/2500000000 : ℝ)*X 2 0+(1080932043/2500000000 : ℝ)*X 2 1+(2161864061/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1732957369/10000000000 : ℝ)*X 0 0+(1269973229/2500000000 : ℝ)*X 0 1+(339636341/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230780063/10000000000 : ℝ)*X 1 0+(-1529556353/10000000000 : ℝ)*X 1 1+(5434181389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230780597/10000000000 : ℝ)*X 2 0+(2717090493/5000000000 : ℝ)*X 2 1+(-764778089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2265572771/5000000000 : ℝ)*X 0 0+(1000340713/2500000000 : ℝ)*X 0 1+(1000340719/2500000000 : ℝ)*X 0 2+(2265572771/5000000000 : ℝ)*X 1 0+(1000340713/2500000000 : ℝ)*X 1 1+(1000340719/2500000000 : ℝ)*X 1 2+(2265572771/5000000000 : ℝ)*X 2 0+(1000340713/2500000000 : ℝ)*X 2 1+(1000340719/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1434584047/10000000000 : ℝ)*X 0 0+(345994159/625000000 : ℝ)*X 0 1+(5196233417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5393828191/10000000000 : ℝ)*X 1 0+(-408044723/2500000000 : ℝ)*X 1 1+(324764567/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5393827993/10000000000 : ℝ)*X 2 0+(5196233053/10000000000 : ℝ)*X 2 1+(-1632179189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((957011701/2500000000 : ℝ)*X 0 0+(4352906171/10000000000 : ℝ)*X 0 1+(4352906077/10000000000 : ℝ)*X 0 2+(957011701/2500000000 : ℝ)*X 1 0+(4352906171/10000000000 : ℝ)*X 1 1+(4352906077/10000000000 : ℝ)*X 1 2+(957011701/2500000000 : ℝ)*X 2 0+(4352906171/10000000000 : ℝ)*X 2 1+(4352906077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1663_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65123/100000 : ℝ) ≤ (-448195280444297761451255424878157/688250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1702813/100000000000000 : ℝ)*(upper1) + (6597423/25000000000000 : ℝ)*(upper4) + (19641303/100000000000000 : ℝ)*(upper5) + (1783568438172459/100000000000000 : ℝ)*(major0) + (1783568438172459/100000000000000 : ℝ)*(major1) + (1783568438172459/100000000000000 : ℝ)*(major2) + (5275530249/100000000000000 : ℝ)*(sp2) + (328173217/50000000000000 : ℝ)*(sp3) + (162879321987187/6250000000000 : ℝ)*(sp4) + (651515731465397/25000000000000 : ℝ)*(sp5) + (260606682528021/10000000000000 : ℝ)*(sp6) + (122846389886057/12500000000000 : ℝ)*(sp7) + (737253867/25000000000000 : ℝ)*(sp8) + (9174948871/100000000000000 : ℝ)*(sp13) + (98277177543489/10000000000000 : ℝ)*(f.failure) + (130303605040523/5000000000000 : ℝ)*(f.sum) + (65937508071451/27530000000000000000000000000 : ℝ)*base65 + (9002236609200822573/1376500000000000000000000000000000 : ℝ)*base67 + (593406258024822573/1376500000000000000000000000000000 : ℝ)*base69 + (14704173129330322573/1376500000000000000000000000000000 : ℝ)*base71 + (97522166224771/27530000000000000000000000000 : ℝ)*base73 + (3916705277946822573/1376500000000000000000000000000000 : ℝ)*base75 + (9044704235785822573/1376500000000000000000000000000000 : ℝ)*base77 + (11374470137244822573/1376500000000000000000000000000000 : ℝ)*base79 + (16352106885441/27530000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (74349/500000000000000000000 : ℝ)*base89 + (74349/500000000000000000000 : ℝ)*base91 + (74349/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29383/50000 : ℝ) ≤ (101118043604856321807215817401631/172062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5520533/50000000000000 : ℝ)*(lower1) + (12898771/50000000000000 : ℝ)*(lower2) + (3922933/100000000000000 : ℝ)*(upper4) + (468953116477109/25000000000000 : ℝ)*(major0) + (468953116477109/25000000000000 : ℝ)*(major1) + (468953116477109/25000000000000 : ℝ)*(major2) + (1349217655396311/50000000000000 : ℝ)*(sp0) + (8432582160803/312500000000 : ℝ)*(sp1) + (674608527093919/25000000000000 : ℝ)*(sp2) + (1033599553324127/100000000000000 : ℝ)*(sp3) + (454543/12500000000000 : ℝ)*(sp7) + (33111363/5000000000000 : ℝ)*(sp8) + (9681562923/100000000000000 : ℝ)*(sp9) + (1864644207/100000000000000 : ℝ)*(sp10) + (1033599556960471/100000000000000 : ℝ)*(f.failure) + (1349217986509941/50000000000000 : ℝ)*(f.sum) + (2051317798033/860312500000000000000000000 : ℝ)*base66 + (1508108641567341123/344125000000000000000000000000000 : ℝ)*base67 + (3375931932721591123/344125000000000000000000000000000 : ℝ)*base69 + (1979819302429783877/344125000000000000000000000000000 : ℝ)*base72 + (2805353320707/13765000000000000000000000000 : ℝ)*base73 + (711686425200466123/344125000000000000000000000000000 : ℝ)*base75 + (244274627469533877/344125000000000000000000000000000 : ℝ)*base78 + (254175943582591123/344125000000000000000000000000000 : ℝ)*base79 + (9690985476891/6882500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6720011/5000000000000000000000 : ℝ)*base89 + (6720011/5000000000000000000000 : ℝ)*base91 + (6720011/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (8143/10000 : ℝ) ≤ (280228881020361917334153975430959/344125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19506569/20000000000000 : ℝ)*(lower3) + (87601391/100000000000000 : ℝ)*(upper4) + (226897/5000000000000 : ℝ)*(lower5) + (983345447141099/50000000000000 : ℝ)*(major0) + (983345447141099/50000000000000 : ℝ)*(major1) + (983345447141099/50000000000000 : ℝ)*(major2) + (443470187/100000000000000 : ℝ)*(sp0) + (1258069103/4000000000000 : ℝ)*(sp1) + (6698659801/50000000000000 : ℝ)*(sp3) + (1411280930033357/50000000000000 : ℝ)*(sp8) + (1411265682621297/50000000000000 : ℝ)*(sp9) + (282256281697017/10000000000000 : ℝ)*(sp10) + (541830738171557/50000000000000 : ℝ)*(sp11) + (128358317/25000000000000 : ℝ)*(sp12) + (270918718415679/25000000000000 : ℝ)*(f.failure) + (282256281697017/10000000000000 : ℝ)*(f.sum) + (22813472290591/13765000000000000000000000000 : ℝ)*base65 + (5130745573232331347/688250000000000000000000000000000 : ℝ)*base68 + (1157947367094918653/688250000000000000000000000000000 : ℝ)*base69 + (1011171534802668653/688250000000000000000000000000000 : ℝ)*base71 + (25026114303487/6882500000000000000000000000 : ℝ)*base74 + (2778763833097831347/688250000000000000000000000000000 : ℝ)*base76 + (4630587166585831347/688250000000000000000000000000000 : ℝ)*base78 + (4362513388271331347/688250000000000000000000000000000 : ℝ)*base80 + (83260673127731/13765000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (842861/1250000000000000000000 : ℝ)*base90 + (842861/1250000000000000000000 : ℝ)*base92 + (842861/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-88349/100000 : ℝ) ≤ (-152010397369881086683749321071307/172062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28211207/25000000000000 : ℝ)*(upper3) + (878003/1250000000000 : ℝ)*(lower4) + (2782003/12500000000000 : ℝ)*(upper5) + (1005726094609527/50000000000000 : ℝ)*(major0) + (1005726094609527/50000000000000 : ℝ)*(major1) + (1005726094609527/50000000000000 : ℝ)*(major2) + (4239998027/100000000000000 : ℝ)*(sp4) + (56298714239/50000000000000 : ℝ)*(sp5) + (121408819367/100000000000000 : ℝ)*(sp6) + (41228978769/100000000000000 : ℝ)*(sp7) + (1472004914078861/50000000000000 : ℝ)*(sp12) + (367987683840909/12500000000000 : ℝ)*(sp13) + (1471946329668191/50000000000000 : ℝ)*(sp14) + (221659551962177/20000000000000 : ℝ)*(sp15) + (554169494394827/50000000000000 : ℝ)*(f.failure) + (11776056272623/400000000000 : ℝ)*(f.sum) + (28855603705853/13765000000000000000000000000 : ℝ)*base65 + (154312130983248769/688250000000000000000000000000000 : ℝ)*base67 + (843134291636751231/688250000000000000000000000000000 : ℝ)*base70 + (2098381899659748769/688250000000000000000000000000000 : ℝ)*base71 + (22600803095381/6882500000000000000000000000 : ℝ)*base74 + (1009681596770998769/688250000000000000000000000000000 : ℝ)*base75 + (5138472760525248769/688250000000000000000000000000000 : ℝ)*base77 + (3553708250647498769/688250000000000000000000000000000 : ℝ)*base79 + (80181444857477/13765000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (6626193/2500000000000000000000 : ℝ)*base90 + (6626193/2500000000000000000000 : ℝ)*base92 + (6626193/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1663_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65123/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29383/50000 : ℝ) else (8143/10000 : ℝ) ≤ X j i ∧ X j i ≤ (88349/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1663_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1663_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (267/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65123/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29383/50000 : ℝ) else (8143/10000 : ℝ) ≤ X j i ∧ X j i ≤ (88349/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1663_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1663_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1663_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4967/1024 : ℝ) ≤ p) (hpb : p ≤ (4971/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90741741/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (267/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65123/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29383/50000 : ℝ) else (8143/10000 : ℝ) ≤ X j i ∧ X j i ≤ (88349/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1663_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
