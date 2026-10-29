-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1669_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:25:17.373104+00:00
-- url     : https://prove2.me/submissions/aae5c1f1-c3df-4280-b923-e45a2d08c8bf

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
theorem support_rectangle_w1669_s3_0 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-391574873/2500000000 : ℝ)*x 0 + (2721008189/5000000000 : ℝ)*x 1 + (5184975951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (391574873/2500000000 : ℝ)^4995 ≤ (9710856409771/100000000000000 : ℝ)^3971 := by
    have hnat : (391574873 : ℕ)^4995*100000000000000^3971 ≤ 9710856409771^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391574873 2500000000 9710856409771 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721008189/5000000000 : ℝ)^4995 ≤ (46517927056683/100000000000000 : ℝ)^3971 := by
    have hnat : (2721008189 : ℕ)^4995*100000000000000^3971 ≤ 46517927056683^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721008189 5000000000 46517927056683 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184975951/10000000000 : ℝ)^4995 ≤ (21885608261151/50000000000000 : ℝ)^3971 := by
    have hnat : (5184975951 : ℕ)^4995*50000000000000^3971 ≤ 21885608261151^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184975951 10000000000 21885608261151 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-391574873/2500000000 : ℝ), (2721008189/5000000000 : ℝ), (5184975951/10000000000 : ℝ)] ![(9710856409771/100000000000000 : ℝ), (46517927056683/100000000000000 : ℝ), (21885608261151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-391574873/2500000000 : ℝ)|^4995 ≤ (9710856409771/100000000000000 : ℝ)^3971
        have hw : |(-391574873/2500000000 : ℝ)|=(391574873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721008189/5000000000 : ℝ)|^4995 ≤ (46517927056683/100000000000000 : ℝ)^3971
        have hw : |(2721008189/5000000000 : ℝ)|=(2721008189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184975951/10000000000 : ℝ)|^4995 ≤ (21885608261151/50000000000000 : ℝ)^3971
        have hw : |(5184975951/10000000000 : ℝ)|=(5184975951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s3_1 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344864747/10000000000 : ℝ)*x 0 + (-212315627/1250000000 : ℝ)*x 1 + (5184975951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344864747/10000000000 : ℝ)^4995 ≤ (22737875662059/50000000000000 : ℝ)^3971 := by
    have hnat : (5344864747 : ℕ)^4995*50000000000000^3971 ≤ 22737875662059^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344864747 10000000000 22737875662059 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212315627/1250000000 : ℝ)^4995 ≤ (2688258034983/25000000000000 : ℝ)^3971 := by
    have hnat : (212315627 : ℕ)^4995*25000000000000^3971 ≤ 2688258034983^3971*1250000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212315627 1250000000 2688258034983 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184975951/10000000000 : ℝ)^4995 ≤ (21885608261151/50000000000000 : ℝ)^3971 := by
    have hnat : (5184975951 : ℕ)^4995*50000000000000^3971 ≤ 21885608261151^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184975951 10000000000 21885608261151 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344864747/10000000000 : ℝ), (-212315627/1250000000 : ℝ), (5184975951/10000000000 : ℝ)] ![(22737875662059/50000000000000 : ℝ), (2688258034983/25000000000000 : ℝ), (21885608261151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344864747/10000000000 : ℝ)|^4995 ≤ (22737875662059/50000000000000 : ℝ)^3971
        have hw : |(5344864747/10000000000 : ℝ)|=(5344864747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212315627/1250000000 : ℝ)|^4995 ≤ (2688258034983/25000000000000 : ℝ)^3971
        have hw : |(-212315627/1250000000 : ℝ)|=(212315627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184975951/10000000000 : ℝ)|^4995 ≤ (21885608261151/50000000000000 : ℝ)^3971
        have hw : |(5184975951/10000000000 : ℝ)|=(5184975951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s3_2 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344864747/10000000000 : ℝ)*x 0 + (5184975951/10000000000 : ℝ)*x 1 + (-212315627/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344864747/10000000000 : ℝ)^4995 ≤ (22737875662059/50000000000000 : ℝ)^3971 := by
    have hnat : (5344864747 : ℕ)^4995*50000000000000^3971 ≤ 22737875662059^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344864747 10000000000 22737875662059 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184975951/10000000000 : ℝ)^4995 ≤ (21885608261151/50000000000000 : ℝ)^3971 := by
    have hnat : (5184975951 : ℕ)^4995*50000000000000^3971 ≤ 21885608261151^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184975951 10000000000 21885608261151 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212315627/1250000000 : ℝ)^4995 ≤ (2688258034983/25000000000000 : ℝ)^3971 := by
    have hnat : (212315627 : ℕ)^4995*25000000000000^3971 ≤ 2688258034983^3971*1250000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212315627 1250000000 2688258034983 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344864747/10000000000 : ℝ), (5184975951/10000000000 : ℝ), (-212315627/1250000000 : ℝ)] ![(22737875662059/50000000000000 : ℝ), (21885608261151/50000000000000 : ℝ), (2688258034983/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344864747/10000000000 : ℝ)|^4995 ≤ (22737875662059/50000000000000 : ℝ)^3971
        have hw : |(5344864747/10000000000 : ℝ)|=(5344864747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184975951/10000000000 : ℝ)|^4995 ≤ (21885608261151/50000000000000 : ℝ)^3971
        have hw : |(5184975951/10000000000 : ℝ)|=(5184975951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212315627/1250000000 : ℝ)|^4995 ≤ (2688258034983/25000000000000 : ℝ)^3971
        have hw : |(-212315627/1250000000 : ℝ)|=(212315627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s3_3 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (833279739/2000000000 : ℝ)*x 0 + (1917864619/5000000000 : ℝ)*x 1 + (903340191/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833279739/2000000000 : ℝ)^4995 ≤ (33243651460039/100000000000000 : ℝ)^3971 := by
    have hnat : (833279739 : ℕ)^4995*100000000000000^3971 ≤ 33243651460039^3971*2000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833279739 2000000000 33243651460039 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1917864619/5000000000 : ℝ)^4995 ≤ (14979765054417/50000000000000 : ℝ)^3971 := by
    have hnat : (1917864619 : ℕ)^4995*50000000000000^3971 ≤ 14979765054417^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917864619 5000000000 14979765054417 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903340191/2000000000 : ℝ)^4995 ≤ (18398409204687/50000000000000 : ℝ)^3971 := by
    have hnat : (903340191 : ℕ)^4995*50000000000000^3971 ≤ 18398409204687^3971*2000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903340191 2000000000 18398409204687 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(833279739/2000000000 : ℝ), (1917864619/5000000000 : ℝ), (903340191/2000000000 : ℝ)] ![(33243651460039/100000000000000 : ℝ), (14979765054417/50000000000000 : ℝ), (18398409204687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(833279739/2000000000 : ℝ)|^4995 ≤ (33243651460039/100000000000000 : ℝ)^3971
        have hw : |(833279739/2000000000 : ℝ)|=(833279739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1917864619/5000000000 : ℝ)|^4995 ≤ (14979765054417/50000000000000 : ℝ)^3971
        have hw : |(1917864619/5000000000 : ℝ)|=(1917864619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903340191/2000000000 : ℝ)|^4995 ≤ (18398409204687/50000000000000 : ℝ)^3971
        have hw : |(903340191/2000000000 : ℝ)|=(903340191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s3_4 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-97897579/625000000 : ℝ)*x 0 + (5186937453/10000000000 : ℝ)*x 1 + (2720017103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97897579/625000000 : ℝ)^4995 ≤ (971133814921/10000000000000 : ℝ)^3971 := by
    have hnat : (97897579 : ℕ)^4995*10000000000000^3971 ≤ 971133814921^3971*625000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97897579 625000000 971133814921 10000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186937453/10000000000 : ℝ)^4995 ≤ (43792046433207/100000000000000 : ℝ)^3971 := by
    have hnat : (5186937453 : ℕ)^4995*100000000000000^3971 ≤ 43792046433207^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186937453 10000000000 43792046433207 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720017103/5000000000 : ℝ)^4995 ≤ (9299323081549/20000000000000 : ℝ)^3971 := by
    have hnat : (2720017103 : ℕ)^4995*20000000000000^3971 ≤ 9299323081549^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720017103 5000000000 9299323081549 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-97897579/625000000 : ℝ), (5186937453/10000000000 : ℝ), (2720017103/5000000000 : ℝ)] ![(971133814921/10000000000000 : ℝ), (43792046433207/100000000000000 : ℝ), (9299323081549/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-97897579/625000000 : ℝ)|^4995 ≤ (971133814921/10000000000000 : ℝ)^3971
        have hw : |(-97897579/625000000 : ℝ)|=(97897579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186937453/10000000000 : ℝ)|^4995 ≤ (43792046433207/100000000000000 : ℝ)^3971
        have hw : |(5186937453/10000000000 : ℝ)|=(5186937453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720017103/5000000000 : ℝ)|^4995 ≤ (9299323081549/20000000000000 : ℝ)^3971
        have hw : |(2720017103/5000000000 : ℝ)|=(2720017103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s3_5 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276057099/10000000000 : ℝ)*x 0 + (-721733383/5000000000 : ℝ)*x 1 + (5440034201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276057099/10000000000 : ℝ)^4995 ≤ (44740574674903/100000000000000 : ℝ)^3971 := by
    have hnat : (5276057099 : ℕ)^4995*100000000000000^3971 ≤ 44740574674903^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276057099 10000000000 44740574674903 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (721733383/5000000000 : ℝ)^4995 ≤ (2190702487317/25000000000000 : ℝ)^3971 := by
    have hnat : (721733383 : ℕ)^4995*25000000000000^3971 ≤ 2190702487317^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721733383 5000000000 2190702487317 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440034201/10000000000 : ℝ)^4995 ≤ (46496615353989/100000000000000 : ℝ)^3971 := by
    have hnat : (5440034201 : ℕ)^4995*100000000000000^3971 ≤ 46496615353989^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440034201 10000000000 46496615353989 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276057099/10000000000 : ℝ), (-721733383/5000000000 : ℝ), (5440034201/10000000000 : ℝ)] ![(44740574674903/100000000000000 : ℝ), (2190702487317/25000000000000 : ℝ), (46496615353989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276057099/10000000000 : ℝ)|^4995 ≤ (44740574674903/100000000000000 : ℝ)^3971
        have hw : |(5276057099/10000000000 : ℝ)|=(5276057099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-721733383/5000000000 : ℝ)|^4995 ≤ (2190702487317/25000000000000 : ℝ)^3971
        have hw : |(-721733383/5000000000 : ℝ)|=(721733383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440034201/10000000000 : ℝ)|^4995 ≤ (46496615353989/100000000000000 : ℝ)^3971
        have hw : |(5440034201/10000000000 : ℝ)|=(5440034201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s3_6 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638028551/5000000000 : ℝ)*x 0 + (2720017101/5000000000 : ℝ)*x 1 + (-1443466761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638028551/5000000000 : ℝ)^4995 ≤ (44740574706903/100000000000000 : ℝ)^3971 := by
    have hnat : (2638028551 : ℕ)^4995*100000000000000^3971 ≤ 44740574706903^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638028551 5000000000 44740574706903 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720017101/5000000000 : ℝ)^4995 ≤ (2324830768237/5000000000000 : ℝ)^3971 := by
    have hnat : (2720017101 : ℕ)^4995*5000000000000^3971 ≤ 2324830768237^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720017101 5000000000 2324830768237 5000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1443466761/10000000000 : ℝ)^4995 ≤ (547675619443/6250000000000 : ℝ)^3971 := by
    have hnat : (1443466761 : ℕ)^4995*6250000000000^3971 ≤ 547675619443^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1443466761 10000000000 547675619443 6250000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638028551/5000000000 : ℝ), (2720017101/5000000000 : ℝ), (-1443466761/10000000000 : ℝ)] ![(44740574706903/100000000000000 : ℝ), (2324830768237/5000000000000 : ℝ), (547675619443/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638028551/5000000000 : ℝ)|^4995 ≤ (44740574706903/100000000000000 : ℝ)^3971
        have hw : |(2638028551/5000000000 : ℝ)|=(2638028551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720017101/5000000000 : ℝ)|^4995 ≤ (2324830768237/5000000000000 : ℝ)^3971
        have hw : |(2720017101/5000000000 : ℝ)|=(2720017101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1443466761/10000000000 : ℝ)|^4995 ≤ (547675619443/6250000000000 : ℝ)^3971
        have hw : |(-1443466761/10000000000 : ℝ)|=(1443466761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s3_7 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4166562343/10000000000 : ℝ)*x 0 + (1127876097/2500000000 : ℝ)*x 1 + (384098057/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166562343/10000000000 : ℝ)^4995 ≤ (16622646963043/50000000000000 : ℝ)^3971 := by
    have hnat : (4166562343 : ℕ)^4995*50000000000000^3971 ≤ 16622646963043^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166562343 10000000000 16622646963043 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127876097/2500000000 : ℝ)^4995 ≤ (3674357368033/10000000000000 : ℝ)^3971 := by
    have hnat : (1127876097 : ℕ)^4995*10000000000000^3971 ≤ 3674357368033^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127876097 2500000000 3674357368033 10000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (384098057/1000000000 : ℝ)^4995 ≤ (7502783093459/25000000000000 : ℝ)^3971 := by
    have hnat : (384098057 : ℕ)^4995*25000000000000^3971 ≤ 7502783093459^3971*1000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384098057 1000000000 7502783093459 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166562343/10000000000 : ℝ), (1127876097/2500000000 : ℝ), (384098057/1000000000 : ℝ)] ![(16622646963043/50000000000000 : ℝ), (3674357368033/10000000000000 : ℝ), (7502783093459/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166562343/10000000000 : ℝ)|^4995 ≤ (16622646963043/50000000000000 : ℝ)^3971
        have hw : |(4166562343/10000000000 : ℝ)|=(4166562343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127876097/2500000000 : ℝ)|^4995 ≤ (3674357368033/10000000000000 : ℝ)^3971
        have hw : |(1127876097/2500000000 : ℝ)|=(1127876097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(384098057/1000000000 : ℝ)|^4995 ≤ (7502783093459/25000000000000 : ℝ)^3971
        have hw : |(384098057/1000000000 : ℝ)|=(384098057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1669_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8143/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5381/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16233/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8143/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5357/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8143/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5357/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8143/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5357/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8143/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5357/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8143/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5357/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8143/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5357/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5357/50000 : ℝ) ^ (4991/1024 : ℝ) ≤ (374103320911493/20000000000000000000 : ℝ) := by
    have hpowers : (5357/50000 : ℝ)^4991 ≤ (374103320911493/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5357 : ℕ)^4991*20000000000000000000^1024 ≤ 374103320911493^1024*50000^4991 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5357 50000 374103320911493 20000000000000000000 4991 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5357/50000 : ℝ)) (X := (374103320911493/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8143/50000 : ℝ) ^ (4991/1024 : ℝ) ≤ (14400085176256429/100000000000000000000 : ℝ) := by
    have hpowers : (8143/50000 : ℝ)^4991 ≤ (14400085176256429/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8143 : ℕ)^4991*100000000000000000000^1024 ≤ 14400085176256429^1024*50000^4991 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8143 50000 14400085176256429 100000000000000000000 4991 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8143/50000 : ℝ)) (X := (14400085176256429/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000374103320911493/10000000000000000000 : ℝ) ≤ (5000038376688569/5000000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (10000374103320911493/10000000000000000000 : ℝ)^1024 ≤ (5000038376688569/5000000000000000 : ℝ)^4991 := by
      have hnat : (10000374103320911493 : ℕ)^1024*5000000000000000^4991 ≤ 5000038376688569^4991*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000374103320911493 10000000000000000000 5000038376688569 5000000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000038376688569/5000000000000000 : ℝ)) (X := (10000374103320911493/10000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50008135300890406947/50000000000000000000 : ℝ) ≤ (78127607822047/78125000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (50008135300890406947/50000000000000000000 : ℝ)^1024 ≤ (78127607822047/78125000000000 : ℝ)^4991 := by
      have hnat : (50008135300890406947 : ℕ)^1024*78125000000000^4991 ≤ 78127607822047^4991*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008135300890406947 50000000000000000000 78127607822047 78125000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78127607822047/78125000000000 : ℝ)) (X := (50008135300890406947/50000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014400085176256429/50000000000000000000 : ℝ) ≤ (5000295424533447/5000000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (50014400085176256429/50000000000000000000 : ℝ)^1024 ≤ (5000295424533447/5000000000000000 : ℝ)^4991 := by
      have hnat : (50014400085176256429 : ℕ)^1024*5000000000000000^4991 ≤ 5000295424533447^4991*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014400085176256429 50000000000000000000 5000295424533447 5000000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000295424533447/5000000000000000 : ℝ)) (X := (50014400085176256429/50000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(374103320911493/20000000000000000000 : ℝ) ≤ ((3482182478037335447/3482500000000000000 : ℝ)+2*(128523922439/278600000000000 : ℝ)*(5357/50000 : ℝ))^(4991/1024 : ℝ) := by
    rw [show (3482182478037335447/3482500000000000000 : ℝ)+2*(128523922439/278600000000000 : ℝ)*(5357/50000 : ℝ)=(5000038376688569/5000000000000000 : ℝ) by norm_num, show 1+2*(374103320911493/20000000000000000000 : ℝ)=(10000374103320911493/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14400085176256429/100000000000000000000 : ℝ)+(374103320911493/20000000000000000000 : ℝ) ≤ ((3482182478037335447/3482500000000000000 : ℝ)+(128523922439/278600000000000 : ℝ)*((8143/50000 : ℝ)+(5357/50000 : ℝ)))^(4991/1024 : ℝ) := by
    rw [show (3482182478037335447/3482500000000000000 : ℝ)+(128523922439/278600000000000 : ℝ)*((8143/50000 : ℝ)+(5357/50000 : ℝ))=(78127607822047/78125000000000 : ℝ) by norm_num, show 1+(14400085176256429/100000000000000000000 : ℝ)+(374103320911493/20000000000000000000 : ℝ)=(50008135300890406947/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14400085176256429/100000000000000000000 : ℝ) ≤ ((3482182478037335447/3482500000000000000 : ℝ)+2*(128523922439/278600000000000 : ℝ)*(8143/50000 : ℝ))^(4991/1024 : ℝ) := by
    rw [show (3482182478037335447/3482500000000000000 : ℝ)+2*(128523922439/278600000000000 : ℝ)*(8143/50000 : ℝ)=(5000295424533447/5000000000000000 : ℝ) by norm_num, show 1+2*(14400085176256429/100000000000000000000 : ℝ)=(50014400085176256429/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3482182478037335447/3482500000000000000 : ℝ)*(X 1 0+X 2 0)+(128523922439/278600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (5357/50000 : ℝ)) (hi := (8143/50000 : ℝ)) (c := (3482182478037335447/3482500000000000000 : ℝ)) (alpha := (128523922439/278600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3482182478037335447/3482500000000000000 : ℝ)*(X 0 1+X 2 1)+(128523922439/278600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (5357/50000 : ℝ)) (hi := (8143/50000 : ℝ)) (c := (3482182478037335447/3482500000000000000 : ℝ)) (alpha := (128523922439/278600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3482182478037335447/3482500000000000000 : ℝ)*(X 0 2+X 1 2)+(128523922439/278600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (5357/50000 : ℝ)) (hi := (8143/50000 : ℝ)) (c := (3482182478037335447/3482500000000000000 : ℝ)) (alpha := (128523922439/278600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-391574873/2500000000 : ℝ)*X 0 0+(2721008189/5000000000 : ℝ)*X 0 1+(5184975951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344864747/10000000000 : ℝ)*X 1 0+(-212315627/1250000000 : ℝ)*X 1 1+(5184975951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344864747/10000000000 : ℝ)*X 2 0+(5184975951/10000000000 : ℝ)*X 2 1+(-212315627/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((833279739/2000000000 : ℝ)*X 0 0+(1917864619/5000000000 : ℝ)*X 0 1+(903340191/2000000000 : ℝ)*X 0 2+(833279739/2000000000 : ℝ)*X 1 0+(1917864619/5000000000 : ℝ)*X 1 1+(903340191/2000000000 : ℝ)*X 1 2+(833279739/2000000000 : ℝ)*X 2 0+(1917864619/5000000000 : ℝ)*X 2 1+(903340191/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-97897579/625000000 : ℝ)*X 0 0+(5186937453/10000000000 : ℝ)*X 0 1+(2720017103/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276057099/10000000000 : ℝ)*X 1 0+(-721733383/5000000000 : ℝ)*X 1 1+(5440034201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638028551/5000000000 : ℝ)*X 2 0+(2720017101/5000000000 : ℝ)*X 2 1+(-1443466761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4166562343/10000000000 : ℝ)*X 0 0+(1127876097/2500000000 : ℝ)*X 0 1+(384098057/1000000000 : ℝ)*X 0 2+(4166562343/10000000000 : ℝ)*X 1 0+(1127876097/2500000000 : ℝ)*X 1 1+(384098057/1000000000 : ℝ)*X 1 2+(4166562343/10000000000 : ℝ)*X 2 0+(1127876097/2500000000 : ℝ)*X 2 1+(384098057/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15593595347227633861942299/6218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (391798923/100000000000000 : ℝ)*(base19) + (183507741/50000000000000 : ℝ)*(base23) + (6623207/50000000000000 : ℝ)*(lower2) + (7646249/12500000000000 : ℝ)*(upper3) + (43582021/100000000000000 : ℝ)*(upper5) + (669867806728477/25000000000000 : ℝ)*(major0) + (669867806728477/25000000000000 : ℝ)*(major1) + (669867806728477/25000000000000 : ℝ)*(major2) + (243152734094107/6250000000000 : ℝ)*(sp0) + (389044835186419/10000000000000 : ℝ)*(sp1) + (389044837664763/10000000000000 : ℝ)*(sp2) + (293698316867809/20000000000000 : ℝ)*(sp3) + (4998157401/100000000000000 : ℝ)*(sp4) + (204224189/10000000000000 : ℝ)*(sp7) + (293698725316187/20000000000000 : ℝ)*(f.failure) + (486306092957889/12500000000000 : ℝ)*(f.sum) + (1847575057143/995000000000000000000000000 : ℝ)*base65 + (55351733411103683/12437500000000000000000000000000 : ℝ)*base68 + (23439155299771317/12437500000000000000000000000000 : ℝ)*base69 + (46206639804896317/12437500000000000000000000000000 : ℝ)*base71 + (210292411599/124375000000000000000000000 : ℝ)*base74 + (122115712851978683/12437500000000000000000000000000 : ℝ)*base76 + (111312105659896317/12437500000000000000000000000000 : ℝ)*base77 + (22773734535208817/12437500000000000000000000000000 : ℝ)*base79 + (706736098233/995000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (11416529/2000000000000000000000 : ℝ)*base90 + (11416529/2000000000000000000000 : ℝ)*base92 + (11416529/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4103113103889138001779/348250000000000000000000000 : ℝ) := by norm_num
    linear_combination (213301573/12500000000000 : ℝ)*(base19) + (1845257869/100000000000000 : ℝ)*(base23) + (24604467/10000000000000 : ℝ)*(upper3) + (1912119/3125000000000 : ℝ)*(lower4) + (122121069/50000000000000 : ℝ)*(upper5) + (54424286791827/2000000000000 : ℝ)*(major0) + (54424286791827/2000000000000 : ℝ)*(major1) + (54424286791827/2000000000000 : ℝ)*(major2) + (20783413343/100000000000000 : ℝ)*(sp1) + (11182494273/50000000000000 : ℝ)*(sp2) + (3951057200199201/100000000000000 : ℝ)*(sp4) + (1975517355186637/50000000000000 : ℝ)*(sp5) + (1975516494976393/50000000000000 : ℝ)*(sp6) + (745685543123569/50000000000000 : ℝ)*(sp7) + (745685543123569/50000000000000 : ℝ)*(f.failure) + (3951057200199201/100000000000000 : ℝ)*(f.sum) + (312728645569/278600000000000000000000000 : ℝ)*base66 + (55919516715450831/6965000000000000000000000000000 : ℝ)*base68 + (2799880652964169/6965000000000000000000000000000 : ℝ)*base69 + (29696285335510831/6965000000000000000000000000000 : ℝ)*base72 + (6104777122331/1393000000000000000000000000 : ℝ)*base74 + (4680508236099169/6965000000000000000000000000000 : ℝ)*base75 + (10448387250465831/6965000000000000000000000000000 : ℝ)*base78 + (21544732943324169/6965000000000000000000000000000 : ℝ)*base79 + (2871839488489/1393000000000000000000000000 : ℝ)*base82 + (4736877/5000000000000000000000 : ℝ)*base89 + (4736877/5000000000000000000000 : ℝ)*base91 + (4736877/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1669_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8143/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16233/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1669_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1669_s4_0 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-156632809/1000000000 : ℝ)*x 0 + (5441869663/10000000000 : ℝ)*x 1 + (324068969/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156632809/1000000000 : ℝ)^4995 ≤ (388443177421/4000000000000 : ℝ)^3971 := by
    have hnat : (156632809 : ℕ)^4995*4000000000000^3971 ≤ 388443177421^3971*1000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156632809 1000000000 388443177421 4000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441869663/10000000000 : ℝ)^4995 ≤ (23258174778787/50000000000000 : ℝ)^3971 := by
    have hnat : (5441869663 : ℕ)^4995*50000000000000^3971 ≤ 23258174778787^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441869663 10000000000 23258174778787 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324068969/625000000 : ℝ)^4995 ≤ (21886285496371/50000000000000 : ℝ)^3971 := by
    have hnat : (324068969 : ℕ)^4995*50000000000000^3971 ≤ 21886285496371^3971*625000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324068969 625000000 21886285496371 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-156632809/1000000000 : ℝ), (5441869663/10000000000 : ℝ), (324068969/625000000 : ℝ)] ![(388443177421/4000000000000 : ℝ), (23258174778787/50000000000000 : ℝ), (21886285496371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-156632809/1000000000 : ℝ)|^4995 ≤ (388443177421/4000000000000 : ℝ)^3971
        have hw : |(-156632809/1000000000 : ℝ)|=(156632809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441869663/10000000000 : ℝ)|^4995 ≤ (23258174778787/50000000000000 : ℝ)^3971
        have hw : |(5441869663/10000000000 : ℝ)|=(5441869663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(324068969/625000000 : ℝ)|^4995 ≤ (21886285496371/50000000000000 : ℝ)^3971
        have hw : |(324068969/625000000 : ℝ)|=(324068969/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s4_1 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213793029/400000000 : ℝ)*x 0 + (-339681657/2000000000 : ℝ)*x 1 + (5185102817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213793029/400000000 : ℝ)^4995 ≤ (2842208356111/6250000000000 : ℝ)^3971 := by
    have hnat : (213793029 : ℕ)^4995*6250000000000^3971 ≤ 2842208356111^3971*400000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213793029 400000000 2842208356111 6250000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339681657/2000000000 : ℝ)^4995 ≤ (5376051290467/50000000000000 : ℝ)^3971 := by
    have hnat : (339681657 : ℕ)^4995*50000000000000^3971 ≤ 5376051290467^3971*2000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339681657 2000000000 5376051290467 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185102817/10000000000 : ℝ)^4995 ≤ (21886281848773/50000000000000 : ℝ)^3971 := by
    have hnat : (5185102817 : ℕ)^4995*50000000000000^3971 ≤ 21886281848773^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185102817 10000000000 21886281848773 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213793029/400000000 : ℝ), (-339681657/2000000000 : ℝ), (5185102817/10000000000 : ℝ)] ![(2842208356111/6250000000000 : ℝ), (5376051290467/50000000000000 : ℝ), (21886281848773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213793029/400000000 : ℝ)|^4995 ≤ (2842208356111/6250000000000 : ℝ)^3971
        have hw : |(213793029/400000000 : ℝ)|=(213793029/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-339681657/2000000000 : ℝ)|^4995 ≤ (5376051290467/50000000000000 : ℝ)^3971
        have hw : |(-339681657/2000000000 : ℝ)|=(339681657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185102817/10000000000 : ℝ)|^4995 ≤ (21886281848773/50000000000000 : ℝ)^3971
        have hw : |(5185102817/10000000000 : ℝ)|=(5185102817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s4_2 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668103223/1250000000 : ℝ)*x 0 + (207404097/400000000 : ℝ)*x 1 + (-1698408731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668103223/1250000000 : ℝ)^4995 ≤ (45475334329213/100000000000000 : ℝ)^3971 := by
    have hnat : (668103223 : ℕ)^4995*100000000000000^3971 ≤ 45475334329213^3971*1250000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668103223 1250000000 45475334329213 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207404097/400000000 : ℝ)^4995 ≤ (4377255953493/10000000000000 : ℝ)^3971 := by
    have hnat : (207404097 : ℕ)^4995*10000000000000^3971 ≤ 4377255953493^3971*400000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207404097 400000000 4377255953493 10000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1698408731/10000000000 : ℝ)^4995 ≤ (2150421226503/20000000000000 : ℝ)^3971 := by
    have hnat : (1698408731 : ℕ)^4995*20000000000000^3971 ≤ 2150421226503^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698408731 10000000000 2150421226503 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668103223/1250000000 : ℝ), (207404097/400000000 : ℝ), (-1698408731/10000000000 : ℝ)] ![(45475334329213/100000000000000 : ℝ), (4377255953493/10000000000000 : ℝ), (2150421226503/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668103223/1250000000 : ℝ)|^4995 ≤ (45475334329213/100000000000000 : ℝ)^3971
        have hw : |(668103223/1250000000 : ℝ)|=(668103223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207404097/400000000 : ℝ)|^4995 ≤ (4377255953493/10000000000000 : ℝ)^3971
        have hw : |(207404097/400000000 : ℝ)|=(207404097/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1698408731/10000000000 : ℝ)|^4995 ≤ (2150421226503/20000000000000 : ℝ)^3971
        have hw : |(-1698408731/10000000000 : ℝ)|=(1698408731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s4_3 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4166417859/10000000000 : ℝ)*x 0 + (3836089383/10000000000 : ℝ)*x 1 + (903267379/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166417859/10000000000 : ℝ)^4995 ≤ (1329753752007/4000000000000 : ℝ)^3971 := by
    have hnat : (4166417859 : ℕ)^4995*4000000000000^3971 ≤ 1329753752007^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166417859 10000000000 1329753752007 4000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3836089383/10000000000 : ℝ)^4995 ≤ (14981534247821/50000000000000 : ℝ)^3971 := by
    have hnat : (3836089383 : ℕ)^4995*50000000000000^3971 ≤ 14981534247821^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3836089383 10000000000 14981534247821 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903267379/2000000000 : ℝ)^4995 ≤ (36793087686509/100000000000000 : ℝ)^3971 := by
    have hnat : (903267379 : ℕ)^4995*100000000000000^3971 ≤ 36793087686509^3971*2000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903267379 2000000000 36793087686509 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166417859/10000000000 : ℝ), (3836089383/10000000000 : ℝ), (903267379/2000000000 : ℝ)] ![(1329753752007/4000000000000 : ℝ), (14981534247821/50000000000000 : ℝ), (36793087686509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166417859/10000000000 : ℝ)|^4995 ≤ (1329753752007/4000000000000 : ℝ)^3971
        have hw : |(4166417859/10000000000 : ℝ)|=(4166417859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3836089383/10000000000 : ℝ)|^4995 ≤ (14981534247821/50000000000000 : ℝ)^3971
        have hw : |(3836089383/10000000000 : ℝ)|=(3836089383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903267379/2000000000 : ℝ)|^4995 ≤ (36793087686509/100000000000000 : ℝ)^3971
        have hw : |(903267379/2000000000 : ℝ)|=(903267379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s4_4 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-783194717/5000000000 : ℝ)*x 0 + (2593530271/5000000000 : ℝ)*x 1 + (1087978437/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (783194717/5000000000 : ℝ)^4995 ≤ (1213944729921/12500000000000 : ℝ)^3971 := by
    have hnat : (783194717 : ℕ)^4995*12500000000000^3971 ≤ 1213944729921^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783194717 5000000000 1213944729921 12500000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593530271/5000000000 : ℝ)^4995 ≤ (8758670725659/20000000000000 : ℝ)^3971 := by
    have hnat : (2593530271 : ℕ)^4995*20000000000000^3971 ≤ 8758670725659^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593530271 5000000000 8758670725659 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087978437/2000000000 : ℝ)^4995 ≤ (46495088522423/100000000000000 : ℝ)^3971 := by
    have hnat : (1087978437 : ℕ)^4995*100000000000000^3971 ≤ 46495088522423^3971*2000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087978437 2000000000 46495088522423 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-783194717/5000000000 : ℝ), (2593530271/5000000000 : ℝ), (1087978437/2000000000 : ℝ)] ![(1213944729921/12500000000000 : ℝ), (8758670725659/20000000000000 : ℝ), (46495088522423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-783194717/5000000000 : ℝ)|^4995 ≤ (1213944729921/12500000000000 : ℝ)^3971
        have hw : |(-783194717/5000000000 : ℝ)|=(783194717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593530271/5000000000 : ℝ)|^4995 ≤ (8758670725659/20000000000000 : ℝ)^3971
        have hw : |(2593530271/5000000000 : ℝ)|=(2593530271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087978437/2000000000 : ℝ)|^4995 ≤ (46495088522423/100000000000000 : ℝ)^3971
        have hw : |(1087978437/2000000000 : ℝ)|=(1087978437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s4_5 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276090709/10000000000 : ℝ)*x 0 + (-360904951/2500000000 : ℝ)*x 1 + (5439892157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276090709/10000000000 : ℝ)^4995 ≤ (44740933180999/100000000000000 : ℝ)^3971 := by
    have hnat : (5276090709 : ℕ)^4995*100000000000000^3971 ≤ 44740933180999^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276090709 10000000000 44740933180999 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (360904951/2500000000 : ℝ)^4995 ≤ (4381989290167/50000000000000 : ℝ)^3971 := by
    have hnat : (360904951 : ℕ)^4995*50000000000000^3971 ≤ 4381989290167^3971*2500000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360904951 2500000000 4381989290167 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439892157/10000000000 : ℝ)^4995 ≤ (2905943013837/6250000000000 : ℝ)^3971 := by
    have hnat : (5439892157 : ℕ)^4995*6250000000000^3971 ≤ 2905943013837^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439892157 10000000000 2905943013837 6250000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276090709/10000000000 : ℝ), (-360904951/2500000000 : ℝ), (5439892157/10000000000 : ℝ)] ![(44740933180999/100000000000000 : ℝ), (4381989290167/50000000000000 : ℝ), (2905943013837/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276090709/10000000000 : ℝ)|^4995 ≤ (44740933180999/100000000000000 : ℝ)^3971
        have hw : |(5276090709/10000000000 : ℝ)|=(5276090709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-360904951/2500000000 : ℝ)|^4995 ≤ (4381989290167/50000000000000 : ℝ)^3971
        have hw : |(-360904951/2500000000 : ℝ)|=(360904951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439892157/10000000000 : ℝ)|^4995 ≤ (2905943013837/6250000000000 : ℝ)^3971
        have hw : |(5439892157/10000000000 : ℝ)|=(5439892157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s4_6 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638045353/5000000000 : ℝ)*x 0 + (2719946091/5000000000 : ℝ)*x 1 + (-721809887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638045353/5000000000 : ℝ)^4995 ≤ (44740933149/100000000000 : ℝ)^3971 := by
    have hnat : (2638045353 : ℕ)^4995*100000000000^3971 ≤ 44740933149^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638045353 5000000000 44740933149 100000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719946091/5000000000 : ℝ)^4995 ≤ (4649508849017/10000000000000 : ℝ)^3971 := by
    have hnat : (2719946091 : ℕ)^4995*10000000000000^3971 ≤ 4649508849017^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719946091 5000000000 4649508849017 10000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (721809887/5000000000 : ℝ)^4995 ≤ (2190994587811/25000000000000 : ℝ)^3971 := by
    have hnat : (721809887 : ℕ)^4995*25000000000000^3971 ≤ 2190994587811^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721809887 5000000000 2190994587811 25000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638045353/5000000000 : ℝ), (2719946091/5000000000 : ℝ), (-721809887/5000000000 : ℝ)] ![(44740933149/100000000000 : ℝ), (4649508849017/10000000000000 : ℝ), (2190994587811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638045353/5000000000 : ℝ)|^4995 ≤ (44740933149/100000000000 : ℝ)^3971
        have hw : |(2638045353/5000000000 : ℝ)|=(2638045353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719946091/5000000000 : ℝ)|^4995 ≤ (4649508849017/10000000000000 : ℝ)^3971
        have hw : |(2719946091/5000000000 : ℝ)|=(2719946091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-721809887/5000000000 : ℝ)|^4995 ≤ (2190994587811/25000000000000 : ℝ)^3971
        have hw : |(-721809887/5000000000 : ℝ)|=(721809887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s4_7 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166663233/400000000 : ℝ)*x 0 + (2255575629/5000000000 : ℝ)*x 1 + (3841329779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166663233/400000000 : ℝ)^4995 ≤ (33245479423181/100000000000000 : ℝ)^3971 := by
    have hnat : (166663233 : ℕ)^4995*100000000000000^3971 ≤ 33245479423181^3971*400000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166663233 400000000 33245479423181 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255575629/5000000000 : ℝ)^4995 ≤ (36739956036171/100000000000000 : ℝ)^3971 := by
    have hnat : (2255575629 : ℕ)^4995*100000000000000^3971 ≤ 36739956036171^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255575629 5000000000 36739956036171 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3841329779/10000000000 : ℝ)^4995 ≤ (15007282262457/50000000000000 : ℝ)^3971 := by
    have hnat : (3841329779 : ℕ)^4995*50000000000000^3971 ≤ 15007282262457^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3841329779 10000000000 15007282262457 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166663233/400000000 : ℝ), (2255575629/5000000000 : ℝ), (3841329779/10000000000 : ℝ)] ![(33245479423181/100000000000000 : ℝ), (36739956036171/100000000000000 : ℝ), (15007282262457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166663233/400000000 : ℝ)|^4995 ≤ (33245479423181/100000000000000 : ℝ)^3971
        have hw : |(166663233/400000000 : ℝ)|=(166663233/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255575629/5000000000 : ℝ)|^4995 ≤ (36739956036171/100000000000000 : ℝ)^3971
        have hw : |(2255575629/5000000000 : ℝ)|=(2255575629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3841329779/10000000000 : ℝ)|^4995 ≤ (15007282262457/50000000000000 : ℝ)^3971
        have hw : |(3841329779/10000000000 : ℝ)|=(3841329779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1669_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16233/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2691/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1623/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16233/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5381/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16233/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5381/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16233/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5381/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16233/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5381/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16233/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5381/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16233/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5381/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5381/50000 : ℝ) ^ (4991/1024 : ℝ) ≤ (382343514400817/20000000000000000000 : ℝ) := by
    have hpowers : (5381/50000 : ℝ)^4991 ≤ (382343514400817/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5381 : ℕ)^4991*20000000000000000000^1024 ≤ 382343514400817^1024*50000^4991 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5381 50000 382343514400817 20000000000000000000 4991 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5381/50000 : ℝ)) (X := (382343514400817/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16233/100000 : ℝ) ^ (4991/1024 : ℝ) ≤ (3543277759767747/25000000000000000000 : ℝ) := by
    have hpowers : (16233/100000 : ℝ)^4991 ≤ (3543277759767747/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16233 : ℕ)^4991*25000000000000000000^1024 ≤ 3543277759767747^1024*100000^4991 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16233 100000 3543277759767747 25000000000000000000 4991 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16233/100000 : ℝ)) (X := (3543277759767747/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000382343514400817/10000000000000000000 : ℝ) ≤ (2000015688792217/2000000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (10000382343514400817/10000000000000000000 : ℝ)^1024 ≤ (2000015688792217/2000000000000000 : ℝ)^4991 := by
      have hnat : (10000382343514400817 : ℕ)^1024*2000000000000000^4991 ≤ 2000015688792217^4991*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000382343514400817 10000000000000000000 2000015688792217 2000000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000015688792217/2000000000000000 : ℝ)) (X := (10000382343514400817/10000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016084828611075073/100000000000000000000 : ℝ) ≤ (250008249755421/250000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (100016084828611075073/100000000000000000000 : ℝ)^1024 ≤ (250008249755421/250000000000000 : ℝ)^4991 := by
      have hnat : (100016084828611075073 : ℕ)^1024*250000000000000^4991 ≤ 250008249755421^4991*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016084828611075073 100000000000000000000 250008249755421 250000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250008249755421/250000000000000 : ℝ)) (X := (100016084828611075073/100000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503543277759767747/12500000000000000000 : ℝ) ≤ (2000116307294519/2000000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (12503543277759767747/12500000000000000000 : ℝ)^1024 ≤ (2000116307294519/2000000000000000 : ℝ)^4991 := by
      have hnat : (12503543277759767747 : ℕ)^1024*2000000000000000^4991 ≤ 2000116307294519^4991*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503543277759767747 12500000000000000000 2000116307294519 2000000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000116307294519/2000000000000000 : ℝ)) (X := (12503543277759767747/12500000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(382343514400817/20000000000000000000 : ℝ) ≤ ((10941002977060445083/10942000000000000000 : ℝ)+2*(50309251151/109420000000000 : ℝ)*(5381/50000 : ℝ))^(4991/1024 : ℝ) := by
    rw [show (10941002977060445083/10942000000000000000 : ℝ)+2*(50309251151/109420000000000 : ℝ)*(5381/50000 : ℝ)=(2000015688792217/2000000000000000 : ℝ) by norm_num, show 1+2*(382343514400817/20000000000000000000 : ℝ)=(10000382343514400817/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3543277759767747/25000000000000000000 : ℝ)+(382343514400817/20000000000000000000 : ℝ) ≤ ((10941002977060445083/10942000000000000000 : ℝ)+(50309251151/109420000000000 : ℝ)*((16233/100000 : ℝ)+(5381/50000 : ℝ)))^(4991/1024 : ℝ) := by
    rw [show (10941002977060445083/10942000000000000000 : ℝ)+(50309251151/109420000000000 : ℝ)*((16233/100000 : ℝ)+(5381/50000 : ℝ))=(250008249755421/250000000000000 : ℝ) by norm_num, show 1+(3543277759767747/25000000000000000000 : ℝ)+(382343514400817/20000000000000000000 : ℝ)=(100016084828611075073/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3543277759767747/25000000000000000000 : ℝ) ≤ ((10941002977060445083/10942000000000000000 : ℝ)+2*(50309251151/109420000000000 : ℝ)*(16233/100000 : ℝ))^(4991/1024 : ℝ) := by
    rw [show (10941002977060445083/10942000000000000000 : ℝ)+2*(50309251151/109420000000000 : ℝ)*(16233/100000 : ℝ)=(2000116307294519/2000000000000000 : ℝ) by norm_num, show 1+2*(3543277759767747/25000000000000000000 : ℝ)=(12503543277759767747/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10941002977060445083/10942000000000000000 : ℝ)*(X 1 0+X 2 0)+(50309251151/109420000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (5381/50000 : ℝ)) (hi := (16233/100000 : ℝ)) (c := (10941002977060445083/10942000000000000000 : ℝ)) (alpha := (50309251151/109420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10941002977060445083/10942000000000000000 : ℝ)*(X 0 1+X 2 1)+(50309251151/109420000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (5381/50000 : ℝ)) (hi := (16233/100000 : ℝ)) (c := (10941002977060445083/10942000000000000000 : ℝ)) (alpha := (50309251151/109420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10941002977060445083/10942000000000000000 : ℝ)*(X 0 2+X 1 2)+(50309251151/109420000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (5381/50000 : ℝ)) (hi := (16233/100000 : ℝ)) (c := (10941002977060445083/10942000000000000000 : ℝ)) (alpha := (50309251151/109420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-156632809/1000000000 : ℝ)*X 0 0+(5441869663/10000000000 : ℝ)*X 0 1+(324068969/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213793029/400000000 : ℝ)*X 1 0+(-339681657/2000000000 : ℝ)*X 1 1+(5185102817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668103223/1250000000 : ℝ)*X 2 0+(207404097/400000000 : ℝ)*X 2 1+(-1698408731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4166417859/10000000000 : ℝ)*X 0 0+(3836089383/10000000000 : ℝ)*X 0 1+(903267379/2000000000 : ℝ)*X 0 2+(4166417859/10000000000 : ℝ)*X 1 0+(3836089383/10000000000 : ℝ)*X 1 1+(903267379/2000000000 : ℝ)*X 1 2+(4166417859/10000000000 : ℝ)*X 2 0+(3836089383/10000000000 : ℝ)*X 2 1+(903267379/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-783194717/5000000000 : ℝ)*X 0 0+(2593530271/5000000000 : ℝ)*X 0 1+(1087978437/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276090709/10000000000 : ℝ)*X 1 0+(-360904951/2500000000 : ℝ)*X 1 1+(5439892157/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638045353/5000000000 : ℝ)*X 2 0+(2719946091/5000000000 : ℝ)*X 2 1+(-721809887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((166663233/400000000 : ℝ)*X 0 0+(2255575629/5000000000 : ℝ)*X 0 1+(3841329779/10000000000 : ℝ)*X 0 2+(166663233/400000000 : ℝ)*X 1 0+(2255575629/5000000000 : ℝ)*X 1 1+(3841329779/10000000000 : ℝ)*X 1 2+(166663233/400000000 : ℝ)*X 2 0+(2255575629/5000000000 : ℝ)*X 2 1+(3841329779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (110443708812547105679804271/13677500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (155310173/6250000000000 : ℝ)*(base19) + (1245881899/50000000000000 : ℝ)*(base23) + (16630037/4000000000000 : ℝ)*(upper3) + (19343349/100000000000000 : ℝ)*(upper4) + (35170067/100000000000000 : ℝ)*(upper5) + (134118010335479/5000000000000 : ℝ)*(major0) + (134118010335479/5000000000000 : ℝ)*(major1) + (134118010335479/5000000000000 : ℝ)*(major2) + (3894623061094211/100000000000000 : ℝ)*(sp0) + (1947320358589809/50000000000000 : ℝ)*(sp1) + (973660177594647/25000000000000 : ℝ)*(sp2) + (367515853725299/25000000000000 : ℝ)*(sp3) + (805641927/4000000000000 : ℝ)*(sp4) + (13527214033/100000000000000 : ℝ)*(sp7) + (1470076942115229/100000000000000 : ℝ)*(f.failure) + (1947321601071193/50000000000000 : ℝ)*(f.sum) + (16133265449901/5471000000000000000000000000 : ℝ)*base65 + (423868534531850243/54710000000000000000000000000000 : ℝ)*base68 + (383531153585760243/54710000000000000000000000000000 : ℝ)*base70 + (91555197230790243/54710000000000000000000000000000 : ℝ)*base72 + (483290514539/683875000000000000000000000 : ℝ)*base74 + (556718732576530243/54710000000000000000000000000000 : ℝ)*base76 + (356419039542389757/54710000000000000000000000000000 : ℝ)*base77 + (632720904361320243/54710000000000000000000000000000 : ℝ)*base80 + (8466848882249/5471000000000000000000000000 : ℝ)*base82 + (22535657/10000000000000000000000 : ℝ)*base89 + (22535657/10000000000000000000000 : ℝ)*base91 + (22535657/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (213970037106849278869592601/17096875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1810055041/100000000000000 : ℝ)*(base19) + (393731743/20000000000000 : ℝ)*(base23) + (138295097/25000000000000 : ℝ)*(lower1) + (130574863/50000000000000 : ℝ)*(upper3) + (8721033/12500000000000 : ℝ)*(lower4) + (51639543/20000000000000 : ℝ)*(upper5) + (42563320987363/1562500000000 : ℝ)*(major0) + (42563320987363/1562500000000 : ℝ)*(major1) + (42563320987363/1562500000000 : ℝ)*(major2) + (2196699917/100000000000000 : ℝ)*(sp2) + (3955178095501809/100000000000000 : ℝ)*(sp4) + (247198517840423/6250000000000 : ℝ)*(sp5) + (494396741267897/12500000000000 : ℝ)*(sp6) + (746463286854403/50000000000000 : ℝ)*(sp7) + (746463286854403/50000000000000 : ℝ)*(f.failure) + (3955178095501809/100000000000000 : ℝ)*(f.sum) + (12239850118127/1367750000000000000000000000 : ℝ)*base65 + (139539712377767379/17096875000000000000000000000000 : ℝ)*base67 + (11412355279428687/2137109375000000000000000000000 : ℝ)*base70 + (1379278142465404879/17096875000000000000000000000000 : ℝ)*base71 + (5439088509959/1367750000000000000000000000 : ℝ)*base73 + (1152189614638807621/17096875000000000000000000000000 : ℝ)*base76 + (85449838123179879/17096875000000000000000000000000 : ℝ)*base77 + (46316976166369627/8548437500000000000000000000000 : ℝ)*base79 + (2194654575101/5471000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (30253001/5000000000000000000000 : ℝ)*base90 + (30253001/5000000000000000000000 : ℝ)*base92 + (30253001/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1669_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16233/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2691/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1623/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1669_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1669_s5_0 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672411279/5000000000 : ℝ)*x 0 + (-849202479/5000000000 : ℝ)*x 1 + (1037021701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672411279/5000000000 : ℝ)^4995 ≤ (4547529980353/10000000000000 : ℝ)^3971 := by
    have hnat : (2672411279 : ℕ)^4995*10000000000000^3971 ≤ 4547529980353^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672411279 5000000000 4547529980353 10000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849202479/5000000000 : ℝ)^4995 ≤ (5376038043709/50000000000000 : ℝ)^3971 := by
    have hnat : (849202479 : ℕ)^4995*50000000000000^3971 ≤ 5376038043709^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849202479 5000000000 5376038043709 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037021701/2000000000 : ℝ)^4995 ≤ (43772624097953/100000000000000 : ℝ)^3971 := by
    have hnat : (1037021701 : ℕ)^4995*100000000000000^3971 ≤ 43772624097953^3971*2000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037021701 2000000000 43772624097953 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672411279/5000000000 : ℝ), (-849202479/5000000000 : ℝ), (1037021701/2000000000 : ℝ)] ![(4547529980353/10000000000000 : ℝ), (5376038043709/50000000000000 : ℝ), (43772624097953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672411279/5000000000 : ℝ)|^4995 ≤ (4547529980353/10000000000000 : ℝ)^3971
        have hw : |(2672411279/5000000000 : ℝ)|=(2672411279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-849202479/5000000000 : ℝ)|^4995 ≤ (5376038043709/50000000000000 : ℝ)^3971
        have hw : |(-849202479/5000000000 : ℝ)|=(849202479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037021701/2000000000 : ℝ)|^4995 ≤ (43772624097953/100000000000000 : ℝ)^3971
        have hw : |(1037021701/2000000000 : ℝ)|=(1037021701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s5_1 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1566391513/10000000000 : ℝ)*x 0 + (2593533229/5000000000 : ℝ)*x 1 + (5439884833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1566391513/10000000000 : ℝ)^4995 ≤ (9711574052963/100000000000000 : ℝ)^3971 := by
    have hnat : (1566391513 : ℕ)^4995*100000000000000^3971 ≤ 9711574052963^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1566391513 10000000000 9711574052963 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593533229/5000000000 : ℝ)^4995 ≤ (43793416455931/100000000000000 : ℝ)^3971 := by
    have hnat : (2593533229 : ℕ)^4995*100000000000000^3971 ≤ 43793416455931^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593533229 5000000000 43793416455931 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439884833/10000000000 : ℝ)^4995 ≤ (23247504740221/50000000000000 : ℝ)^3971 := by
    have hnat : (5439884833 : ℕ)^4995*50000000000000^3971 ≤ 23247504740221^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439884833 10000000000 23247504740221 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1566391513/10000000000 : ℝ), (2593533229/5000000000 : ℝ), (5439884833/10000000000 : ℝ)] ![(9711574052963/100000000000000 : ℝ), (43793416455931/100000000000000 : ℝ), (23247504740221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1566391513/10000000000 : ℝ)|^4995 ≤ (9711574052963/100000000000000 : ℝ)^3971
        have hw : |(-1566391513/10000000000 : ℝ)|=(1566391513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593533229/5000000000 : ℝ)|^4995 ≤ (43793416455931/100000000000000 : ℝ)^3971
        have hw : |(2593533229/5000000000 : ℝ)|=(2593533229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439884833/10000000000 : ℝ)|^4995 ≤ (23247504740221/50000000000000 : ℝ)^3971
        have hw : |(5439884833/10000000000 : ℝ)|=(5439884833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s5_2 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276092141/10000000000 : ℝ)*x 0 + (-1443628129/10000000000 : ℝ)*x 1 + (679985603/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276092141/10000000000 : ℝ)^4995 ≤ (8948189691131/20000000000000 : ℝ)^3971 := by
    have hnat : (5276092141 : ℕ)^4995*20000000000000^3971 ≤ 8948189691131^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276092141 10000000000 8948189691131 20000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1443628129/10000000000 : ℝ)^4995 ≤ (8764042152739/100000000000000 : ℝ)^3971 := by
    have hnat : (1443628129 : ℕ)^4995*100000000000000^3971 ≤ 8764042152739^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1443628129 10000000000 8764042152739 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679985603/1250000000 : ℝ)^4995 ≤ (23247504691841/50000000000000 : ℝ)^3971 := by
    have hnat : (679985603 : ℕ)^4995*50000000000000^3971 ≤ 23247504691841^3971*1250000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679985603 1250000000 23247504691841 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276092141/10000000000 : ℝ), (-1443628129/10000000000 : ℝ), (679985603/1250000000 : ℝ)] ![(8948189691131/20000000000000 : ℝ), (8764042152739/100000000000000 : ℝ), (23247504691841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276092141/10000000000 : ℝ)|^4995 ≤ (8948189691131/20000000000000 : ℝ)^3971
        have hw : |(5276092141/10000000000 : ℝ)|=(5276092141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1443628129/10000000000 : ℝ)|^4995 ≤ (8764042152739/100000000000000 : ℝ)^3971
        have hw : |(-1443628129/10000000000 : ℝ)|=(1443628129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679985603/1250000000 : ℝ)|^4995 ≤ (23247504691841/50000000000000 : ℝ)^3971
        have hw : |(679985603/1250000000 : ℝ)|=(679985603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s5_3 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055218429/2000000000 : ℝ)*x 0 + (2719942393/5000000000 : ℝ)*x 1 + (-1443628177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055218429/2000000000 : ℝ)^4995 ≤ (22370474249161/50000000000000 : ℝ)^3971 := by
    have hnat : (1055218429 : ℕ)^4995*50000000000000^3971 ≤ 22370474249161^3971*2000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055218429 2000000000 22370474249161 50000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719942393/5000000000 : ℝ)^4995 ≤ (46495008975141/100000000000000 : ℝ)^3971 := by
    have hnat : (2719942393 : ℕ)^4995*100000000000000^3971 ≤ 46495008975141^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719942393 5000000000 46495008975141 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1443628177/10000000000 : ℝ)^4995 ≤ (8764042519283/100000000000000 : ℝ)^3971 := by
    have hnat : (1443628177 : ℕ)^4995*100000000000000^3971 ≤ 8764042519283^3971*10000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1443628177 10000000000 8764042519283 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055218429/2000000000 : ℝ), (2719942393/5000000000 : ℝ), (-1443628177/10000000000 : ℝ)] ![(22370474249161/50000000000000 : ℝ), (46495008975141/100000000000000 : ℝ), (8764042519283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055218429/2000000000 : ℝ)|^4995 ≤ (22370474249161/50000000000000 : ℝ)^3971
        have hw : |(1055218429/2000000000 : ℝ)|=(1055218429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719942393/5000000000 : ℝ)|^4995 ≤ (46495008975141/100000000000000 : ℝ)^3971
        have hw : |(2719942393/5000000000 : ℝ)|=(2719942393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1443628177/10000000000 : ℝ)|^4995 ≤ (8764042519283/100000000000000 : ℝ)^3971
        have hw : |(-1443628177/10000000000 : ℝ)|=(1443628177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1669_s5_4 (p : ℝ) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (416658171/1000000000 : ℝ)*x 0 + (180445341/400000000 : ℝ)*x 1 + (1920673679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416658171/1000000000 : ℝ)^4995 ≤ (33245488305609/100000000000000 : ℝ)^3971 := by
    have hnat : (416658171 : ℕ)^4995*100000000000000^3971 ≤ 33245488305609^3971*1000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416658171 1000000000 33245488305609 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180445341/400000000 : ℝ)^4995 ≤ (4592471796523/12500000000000 : ℝ)^3971 := by
    have hnat : (180445341 : ℕ)^4995*12500000000000^3971 ≤ 4592471796523^3971*400000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180445341 400000000 4592471796523 12500000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1920673679/5000000000 : ℝ)^4995 ≤ (30014737299747/100000000000000 : ℝ)^3971 := by
    have hnat : (1920673679 : ℕ)^4995*100000000000000^3971 ≤ 30014737299747^3971*5000000000^4995 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920673679 5000000000 30014737299747 100000000000000 4995 3971 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4995/1024 : ℝ)) 4995 3971 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(416658171/1000000000 : ℝ), (180445341/400000000 : ℝ), (1920673679/5000000000 : ℝ)] ![(33245488305609/100000000000000 : ℝ), (4592471796523/12500000000000 : ℝ), (30014737299747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(416658171/1000000000 : ℝ)|^4995 ≤ (33245488305609/100000000000000 : ℝ)^3971
        have hw : |(416658171/1000000000 : ℝ)|=(416658171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180445341/400000000 : ℝ)|^4995 ≤ (4592471796523/12500000000000 : ℝ)^3971
        have hw : |(180445341/400000000 : ℝ)|=(180445341/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1920673679/5000000000 : ℝ)|^4995 ≤ (30014737299747/100000000000000 : ℝ)^3971
        have hw : |(1920673679/5000000000 : ℝ)|=(1920673679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1669_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1623/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2691/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2691/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16229/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1623/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2691/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1623/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2691/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1623/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2691/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1623/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2691/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1623/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2691/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1623/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2691/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2691/25000 : ℝ) ^ (4991/1024 : ℝ) ≤ (1913449798539027/100000000000000000000 : ℝ) := by
    have hpowers : (2691/25000 : ℝ)^4991 ≤ (1913449798539027/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2691 : ℕ)^4991*100000000000000000000^1024 ≤ 1913449798539027^1024*25000^4991 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2691 25000 1913449798539027 100000000000000000000 4991 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2691/25000 : ℝ)) (X := (1913449798539027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1623/10000 : ℝ) ^ (4991/1024 : ℝ) ≤ (14160349007891951/100000000000000000000 : ℝ) := by
    have hpowers : (1623/10000 : ℝ)^4991 ≤ (14160349007891951/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1623 : ℕ)^4991*100000000000000000000^1024 ≤ 14160349007891951^1024*10000^4991 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1623 10000 14160349007891951 100000000000000000000 4991 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1623/10000 : ℝ)) (X := (14160349007891951/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001913449798539027/50000000000000000000 : ℝ) ≤ (10000078515038867/10000000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (50001913449798539027/50000000000000000000 : ℝ)^1024 ≤ (10000078515038867/10000000000000000 : ℝ)^4991 := by
      have hnat : (50001913449798539027 : ℕ)^1024*10000000000000000^4991 ≤ 10000078515038867^4991*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001913449798539027 50000000000000000000 10000078515038867 10000000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000078515038867/10000000000000000 : ℝ)) (X := (50001913449798539027/50000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50008036899403215489/50000000000000000000 : ℝ) ≤ (10000329763948023/10000000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (50008036899403215489/50000000000000000000 : ℝ)^1024 ≤ (10000329763948023/10000000000000000 : ℝ)^4991 := by
      have hnat : (50008036899403215489 : ℕ)^1024*10000000000000000^4991 ≤ 10000329763948023^4991*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008036899403215489 50000000000000000000 10000329763948023 10000000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000329763948023/10000000000000000 : ℝ)) (X := (50008036899403215489/50000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014160349007891951/50000000000000000000 : ℝ) ≤ (10000581012857179/10000000000000000 : ℝ) ^ (4991/1024 : ℝ) := by
    have hpowers : (50014160349007891951/50000000000000000000 : ℝ)^1024 ≤ (10000581012857179/10000000000000000 : ℝ)^4991 := by
      have hnat : (50014160349007891951 : ℕ)^1024*10000000000000000^4991 ≤ 10000581012857179^4991*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014160349007891951 50000000000000000000 10000581012857179 10000000000000000 1024 4991 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000581012857179/10000000000000000 : ℝ)) (X := (50014160349007891951/50000000000000000000 : ℝ)) (by norm_num) 4991 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1913449798539027/100000000000000000000 : ℝ) ≤ ((9109170046114356109/9110000000000000000 : ℝ)+2*(62812227289/136650000000000 : ℝ)*(2691/25000 : ℝ))^(4991/1024 : ℝ) := by
    rw [show (9109170046114356109/9110000000000000000 : ℝ)+2*(62812227289/136650000000000 : ℝ)*(2691/25000 : ℝ)=(10000078515038867/10000000000000000 : ℝ) by norm_num, show 1+2*(1913449798539027/100000000000000000000 : ℝ)=(50001913449798539027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14160349007891951/100000000000000000000 : ℝ)+(1913449798539027/100000000000000000000 : ℝ) ≤ ((9109170046114356109/9110000000000000000 : ℝ)+(62812227289/136650000000000 : ℝ)*((1623/10000 : ℝ)+(2691/25000 : ℝ)))^(4991/1024 : ℝ) := by
    rw [show (9109170046114356109/9110000000000000000 : ℝ)+(62812227289/136650000000000 : ℝ)*((1623/10000 : ℝ)+(2691/25000 : ℝ))=(10000329763948023/10000000000000000 : ℝ) by norm_num, show 1+(14160349007891951/100000000000000000000 : ℝ)+(1913449798539027/100000000000000000000 : ℝ)=(50008036899403215489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14160349007891951/100000000000000000000 : ℝ) ≤ ((9109170046114356109/9110000000000000000 : ℝ)+2*(62812227289/136650000000000 : ℝ)*(1623/10000 : ℝ))^(4991/1024 : ℝ) := by
    rw [show (9109170046114356109/9110000000000000000 : ℝ)+2*(62812227289/136650000000000 : ℝ)*(1623/10000 : ℝ)=(10000581012857179/10000000000000000 : ℝ) by norm_num, show 1+2*(14160349007891951/100000000000000000000 : ℝ)=(50014160349007891951/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9109170046114356109/9110000000000000000 : ℝ)*(X 1 0+X 2 0)+(62812227289/136650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (2691/25000 : ℝ)) (hi := (1623/10000 : ℝ)) (c := (9109170046114356109/9110000000000000000 : ℝ)) (alpha := (62812227289/136650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9109170046114356109/9110000000000000000 : ℝ)*(X 0 1+X 2 1)+(62812227289/136650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (2691/25000 : ℝ)) (hi := (1623/10000 : ℝ)) (c := (9109170046114356109/9110000000000000000 : ℝ)) (alpha := (62812227289/136650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9109170046114356109/9110000000000000000 : ℝ)*(X 0 2+X 1 2)+(62812227289/136650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4991/1024 : ℝ)) (lo := (2691/25000 : ℝ)) (hi := (1623/10000 : ℝ)) (c := (9109170046114356109/9110000000000000000 : ℝ)) (alpha := (62812227289/136650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2672411279/5000000000 : ℝ)*X 1 0+(-849202479/5000000000 : ℝ)*X 1 1+(1037021701/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s5_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1566391513/10000000000 : ℝ)*X 0 0+(2593533229/5000000000 : ℝ)*X 0 1+(5439884833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s5_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5276092141/10000000000 : ℝ)*X 1 0+(-1443628129/10000000000 : ℝ)*X 1 1+(679985603/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s5_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1055218429/2000000000 : ℝ)*X 2 0+(2719942393/5000000000 : ℝ)*X 2 1+(-1443628177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s5_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((416658171/1000000000 : ℝ)*X 0 0+(180445341/400000000 : ℝ)*X 0 1+(1920673679/5000000000 : ℝ)*X 0 2+(416658171/1000000000 : ℝ)*X 1 0+(180445341/400000000 : ℝ)*X 1 1+(1920673679/5000000000 : ℝ)*X 1 2+(416658171/1000000000 : ℝ)*X 2 0+(180445341/400000000 : ℝ)*X 2 1+(1920673679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1669_s5_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (165781790603000019600055033/56937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (404658389/100000000000000 : ℝ)*(base19) + (397274169/100000000000000 : ℝ)*(base23) + (101044249/100000000000000 : ℝ)*(lower1) + (13218717/25000000000000 : ℝ)*(upper3) + (363809/20000000000000 : ℝ)*(lower4) + (35661669/50000000000000 : ℝ)*(upper5) + (681052165331321/25000000000000 : ℝ)*(major0) + (681052165331321/25000000000000 : ℝ)*(major1) + (681052165331321/25000000000000 : ℝ)*(major2) + (530855919/50000000000000 : ℝ)*(sp0) + (123606409087333/3125000000000 : ℝ)*(sp1) + (395540362442443/10000000000000 : ℝ)*(sp2) + (1977702346760243/50000000000000 : ℝ)*(sp3) + (186626516850133/12500000000000 : ℝ)*(sp4) + (186626516850133/12500000000000 : ℝ)*(f.failure) + (123606409087333/3125000000000 : ℝ)*(f.sum) + (3082996859041/1708125000000000000000000000 : ℝ)*base66 + (5119799025903969967/683250000000000000000000000000000 : ℝ)*base67 + (9456713156229969967/683250000000000000000000000000000 : ℝ)*base69 + (317462553689469967/683250000000000000000000000000000 : ℝ)*base71 + (10625202902681/6832500000000000000000000000 : ℝ)*base73 + (1798450471131530033/683250000000000000000000000000000 : ℝ)*base76 + (9902273770442469967/683250000000000000000000000000000 : ℝ)*base77 + (12042844991232969967/683250000000000000000000000000000 : ℝ)*base79 + (12119291560849/6832500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (11246911/1250000000000000000000 : ℝ)*base90 + (11246911/1250000000000000000000 : ℝ)*base92 + (11246911/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1669_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1623/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2691/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2691/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16229/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1669_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1669_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8143/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2691/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16229/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1669_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1669_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1669_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4991/1024 : ℝ) ≤ p) (hpb : p ≤ (4995/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182463933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8143/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2691/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16229/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1669_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
